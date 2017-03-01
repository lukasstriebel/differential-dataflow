#!/usr/bin/env python

import argparse
import itertools
import multiprocessing
import os
import re
import socket
import subprocess
from collections import namedtuple

try:
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_pdf import PdfPages
    import matplotlib
    import numpy
except Exception as e:
    print(e)
    print('Plotting unavailable')

# Allows to describe an object
def auto_str(cls):
    def __str__(self):
        return '%s(%s)' % (
            type(self).__name__,
            ', '.join('%s=%s' % item for item in vars(self).items())
        )
    cls.__str__ = __str__
    return cls

def autolabel(rects, ax, f=lambda x: '%d' % int(x)):
    """
    Attach a text label above each bar displaying its height
    """
    for rect in rects:
        height = rect.get_height()
        ax.text(rect.get_x() + rect.get_width()/2., height,
                f(height),
                ha='center', va='bottom', size=7)

class BenchmarkException(Exception):
    def __init__(self, reason):
        self.reason = reason

class ProcessExecuter(object):

    def execute(self, command, **kwargs):
        print(command)
        # Filter None parameters
        return subprocess.Popen([ str(c) for c in command if c is not None ], **kwargs)

@auto_str
class BenchmarkBinary(object):
    def __init__(self, binary, mode):
        self.binary = binary
        self.mode = mode

class BenchmarkBinaryFactory(object):
    def __init__(self, binary):
        self.binary = binary
        # Set to None if not release mode...
        self.mode = '--release'

    def build(self):
        pe = ProcessExecuter()
        command = ['cargo', 'build', self.mode, '--example', self.binary]
        pe.execute(command).communicate()
        return BenchmarkBinary(self.binary, self.mode)

@auto_str
class StaticConfiguration(object):
    def __init__(self, topology, prepareBinary, binary, switches, ports, hosts, batches, prefix):
        self.topology = topology
        self.prepareBinary = prepareBinary
        self.binary = binary
        self.switches = switches
        self.ports = ports
        self.hosts = hosts
        self.batches = batches

        self.prefix = prefix

    def getDirName(self):
        t = (self.prefix, self.binary, self.topology, self.hosts, self.switches,
             self.ports, self.batches)
        # prefix_binary_topology_hosts_switches_ports_batches
        return "%s_%s_%s_%i_%i_%i_%i" % t

@auto_str
class Configuration(object):
    def __init__(self, workers, batchSize, changeRatio, name, staticConfig, batches=None):
        self.workers = workers
        self.batchSize = batchSize
        self.name = name
        self.changeRatio = changeRatio
        if batches is None:
            self.batches = staticConfig.batches
        else:
            self.batches = batches

        self.staticConfig = staticConfig

    def getFileName(self):
        t = (self.staticConfig.getDirName(), self.name, self.batchSize, self.changeRatio, self.workers)
        # prefix_binary_topology_hosts_switches_ports_batches/raw_batchSize_changeRatio_workers.txt
        return "%s/%s_%i_%i_%i.txt" % t

@auto_str
class BenchmarkData(object):
    def __init__(self):
        self.initial = None
        self.initialChanges = None
        self.incremental = []
        self.changes = []
        self.incrementalArray = None
        self.incrementalMedian = None

class Benchmark(object):
    def __init__(self, configuration, binary):
        self.configuration = configuration
        self.binary = binary

    def _saveData(self, data):
        fileName = self.configuration.getFileName()
        dirName = os.path.dirname(fileName)
        if not os.path.isdir(dirName):
            os.mkdir(dirName)
        with open(fileName, 'wb') as f:
            f.write(data)

    def run(self):
        # Do not try to re-run experiment...
        saveFile = self.configuration.getFileName()
        if os.path.isfile(self.configuration.getFileName()):
            with open(saveFile, 'rb') as f:
                stdoutdata = f.read()
            print('Not re-running experiment for %s.' % (saveFile))
        else:
            print('Running experiment for %s.' % (saveFile))
            static = self.configuration.staticConfig
            command = ['cargo', 'run', self.binary.mode, '--example', self.binary.binary,
                       static.topology, static.hosts, static.switches,
                       static.ports, self.configuration.batches,
                       self.configuration.batchSize, self.configuration.changeRatio,
                       '--', '-w', self.configuration.workers]
            popen = ProcessExecuter().execute(command, stdout=subprocess.PIPE)
            (stdoutdata, _) = popen.communicate()
            if popen.returncode != 0:
                raise BenchmarkException(str(popen.returncode))
            self._saveData(stdoutdata)

class BenchmarkParser(object):

    def read(self, configuration):
        saveFile = configuration.getFileName()
        with open(saveFile, 'rb') as f:
            stdoutdata = f.read()
        return self._parseData(stdoutdata, configuration)

    def _processData(self, data, configuration):
        data.incrementalArray = numpy.array([ v * 1000 for v in data.incremental ])
        data.incrementalMedian = numpy.median(data.incrementalArray)
        p = numpy.percentile(data.incrementalArray, [ 95 ])
        if configuration.changeRatio is 40 and p <= 1000:
            print((configuration.workers, configuration.batchSize, ))
        if configuration.changeRatio is 5 and configuration.workers is 1 and configuration.batchSize is 1:
            print(p)
        data.throughput = 1000.0 * configuration.batchSize / data.incrementalMedian

    def _parseData(self, stdoutdata, configuration):
        data = BenchmarkData()
        changes = 0
        for line in stdoutdata.splitlines():
            if line.startswith("stable; elapsed: ") and data.initial is None:
                data.inital = float(re.findall("\\d+[.]\\d+", line)[0])
                data.initialChanges = changes
                changes = 0
            elif line.startswith("Changes: "):
                changes = changes + int(re.findall("\\d+", line)[0])
            elif line.startswith("batch "):
                time = re.findall("\\d+[.]\\d+", line)[0]
                data.incremental.append(float(time))
                data.changes.append(changes)
                changes = 0

        self._processData(data, configuration)

        return data

class BenchmarkAction(object):

    def __init__(self, staticConfig):
        self.staticConfig = staticConfig

    def powersOfTwo(self, limit, start=1):
        num = start
        while num <= limit:
            yield num
            num = num * 2

class RunBenchmark(BenchmarkAction):
    def __init__(self, staticConfig, args):
        super(RunBenchmark, self).__init__(staticConfig)
        self.prepareBinary = BenchmarkBinaryFactory(staticConfig.prepareBinary).build()
        self.binary = BenchmarkBinaryFactory(staticConfig.binary).build()
        self.args = args
        self.results = {}

    def doBenchmarks(self):
        for workers in reversed(list(self.powersOfTwo(args.maxWorkers))):
            config = Configuration(workers=workers, batchSize=1, changeRatio=1, staticConfig=self.staticConfig, name='prepare', batches=0)
            benchmark = Benchmark(config, self.prepareBinary)
            benchmark.run()
            for batchSize in self.powersOfTwo(args.maxBatchSize):
                for changes in args.changeRatios:
                    config = Configuration(workers=workers, batchSize=batchSize, changeRatio=changes, staticConfig=self.staticConfig, name='raw')
                    benchmark = Benchmark(config, self.binary)
                    benchmark.run()

class Analysis(BenchmarkAction):

    def __init__(self, name, staticConfig, args):
        super(Analysis, self).__init__(staticConfig)
        self.name = name
        self.data = self._readData(args)

    def _outputFileName(self, *args):
        fileName = self.name + '_'.join(map(str, args[:-1])) + "." + args[-1]
        directory = os.path.dirname(fileName)
        if not os.path.exists(directory):
            os.mkdir(directory)
        return fileName

    def _readData(self, args):
        parser = BenchmarkParser()
        data = {}
        for workers in self.powersOfTwo(args.maxWorkers):
            for batchSize in self.powersOfTwo(args.maxBatchSize):
                for changes in args.changeRatios:
                    config = Configuration(workers=workers, batchSize=batchSize, changeRatio=changes, staticConfig=self.staticConfig, name='raw')
                    data[config] = parser.read(config)
        return data

Index = namedtuple('Index', ['changeRatio', 'workers', 'batchSize'])

class Plotter(Analysis):

    MARKERS = [ 's', 'o', 'D', '1', 'x', 'd', 'p', 'v', '^', '8', '+' ]

    def __init__(self, name, staticConfig, args):
        super(Plotter, self).__init__(name, staticConfig, args)
        self.axis = None
        self.figure = None
        self.allChangeRatios = set()
        self.allWorkers = set()
        self.allBatchSizes = set()

    def _convertData(self):
        converted = {}
        for config, data in self.data.iteritems():
            idx = Index(config.changeRatio, config.workers, config.batchSize)
            converted[idx] = data
            self.allChangeRatios.add(config.changeRatio)
            self.allWorkers.add(config.workers)
            self.allBatchSizes.add(config.batchSize)
        self._groupedData = converted
        self.allChangeRatios = sorted(self.allChangeRatios)
        self.allBatchSizes = sorted(self.allBatchSizes)
        self.allWorkers = sorted(self.allWorkers)

    def _plotSingle_workers_batchSize(self, workers, batchSize):
        dataObjs = [ self._groupedData[Index(changeRatio, workers, batchSize)]
                    for changeRatio in self.allChangeRatios ]
        data = [ d.incrementalArray for d in dataObjs ]

        # Plot box plot, fixed worker
        with PdfPages(self._outputFileName("workers", workers, "batchSize", batchSize, "box-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            ax.boxplot(data)
            ax.set_xlabel('Weight change ratio')
            ax.set_xticklabels(self.allChangeRatios)
            ax.set_ylabel('Update latency [ms]')
            ax.set_ylim(bottom=0, top=100)
            ax.axhline(50, color='b', linestyle='dotted', linewidth=1)

            pdf.savefig(bbox_inches='tight')
            plt.close()

    def _plotSingle_changeRatio_batchSize(self, changeRatio, batchSize):
        dataObjs = [ self._groupedData[Index(changeRatio, workers, batchSize)]
                    for workers in self.allWorkers ]
        data = [ d.incrementalArray for d in dataObjs ]

        # Plot box plot, fixed worker
        with PdfPages(self._outputFileName("changeRatio", changeRatio, "batchSize", batchSize, "box-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            ax.boxplot(data)
            ax.set_xlabel('Workers')
            ax.set_xticklabels(self.allBatchSizes)
            ax.set_ylabel('Update latency [ms]')

            pdf.savefig(bbox_inches='tight')
            plt.close()

    def _plotSingle_changeRatio_workers(self, changeRatio, workers):
        dataObjs = [ self._groupedData[Index(changeRatio, workers, batchSize)]
                    for batchSize in self.allBatchSizes ]
        data = [ d.incrementalArray for d in dataObjs ]

        # Plot box plot, fixed worker
        with PdfPages(self._outputFileName("changeRatio", changeRatio, "workers", workers, "box-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            ax.boxplot(data)
            ax.set_xlabel('Batch size')
            ax.set_xticklabels(self.allBatchSizes)
            ax.set_ylabel('Update latency [ms]')

            pdf.savefig(bbox_inches='tight')
            plt.close()

        # Plot scatter plot latency vs. throughput
        latency = [ d.incrementalMedian for d in dataObjs ]
        throughput = [ d.throughput for d in dataObjs ]

        with PdfPages(self._outputFileName("changeRatio", changeRatio, "workers", workers, "scatter-latency-throughput", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            ax.scatter(latency, throughput)
            ax.set_xlabel('Median update latency [ms]')
            ax.set_ylabel('Throughput [updates/s]')

            pdf.savefig(bbox_inches='tight')
            plt.close()

        # Plot scatter plot changes vs. latency
        changes = [ d.changes for d in dataObjs ]
        latencys = [ d.incremental for d in dataObjs ]

        with PdfPages(self._outputFileName("changeRatio", changeRatio, "workers", workers, "scatter-changes-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            for change, latency, i in zip(changes, latencys, itertools.count()):
                ax.scatter(change, latency, s=1, label=('Batch size %i.' % (self.allBatchSizes[i])))
            ax.set_xlabel('Number of changes per batch')
            ax.set_ylabel('Latency [ms]')
            ax.legend()

            pdf.savefig(bbox_inches='tight')
            plt.close()

    def _plotMultipleInit(self):
        figure, axis = plt.subplots(1, sharex=False, sharey=False)
        self.sameBatch = {}
        return figure, axis

    def _plotMultipleScatter(self, axis, changeRatio, workers, label, i):
        dataObjs = [ self._groupedData[Index(changeRatio, workers, batchSize)] for batchSize in self.allBatchSizes ]
        # Plot scatter plot
        latency = [ d.incrementalMedian for d in dataObjs ]
        throughput = [ d.throughput for d in dataObjs ]
        axis.plot(latency, throughput, label=label, zorder=1)
        for i, x in enumerate(latency):
            point = (x, throughput[i])
            batch = self.sameBatch.get(self.allBatchSizes[i], [])
            if not batch:
                axis.annotate(self.allBatchSizes[i], point)
            batch.append(point)
            self.sameBatch[self.allBatchSizes[i]] = batch

    def _plotMultipleMedian(self, axis, changeRatio, workers, label, i):
        dataObjs = [ self._groupedData[Index(changeRatio, workers, batchSize)] for batchSize in self.allBatchSizes ]
        # Plot scatter plot
        latency = [ d.incrementalMedian for d in dataObjs ]
        axis.plot(latency, markersize=4, marker=self.MARKERS[i], label=label,
                  zorder=1, linestyle='--', markerfacecolor='None')


    def _plotMultipleDoneScatter(self, figure, axis, f):
        for batchSize in sorted(self.sameBatch):
            batch = self.sameBatch[batchSize]
            batch = sorted(batch)
            axis.plot([ b[0] for b in batch], [ b[1] for b in batch],
                    color='grey', zorder=0, linewidth=.1)
        axis.set_xlabel('Median update latency [ms]')
        axis.set_ylabel('Throughput [updates/s]')
        axis.legend()
        self._plotMultipleDone(figure, axis, f)

    def _plotMultipleDoneMedian(self, figure, axis, f):
        axis.set_xlabel('Batch size')
        axis.set_xticks(range(len(self.allBatchSizes)))
        axis.set_xticklabels(self.allBatchSizes)
        axis.set_ylabel('Median update latency [ms]')
        axis.set_ylim(bottom=0, top=1000)
        axis.axhline(50, color='b', linestyle='dotted', linewidth=1)
        axis.legend()
        self._plotMultipleDone(figure, axis, f)

    def _plotMultipleDone(self, figure, axis, f):
        with PdfPages(f) as pdf:
            pdf.savefig(bbox_inches='tight', figure=figure)
        plt.close(figure)

    def plot(self):
        # convert data into semi-usable format
        self._convertData()
        for workers, batchSize in itertools.product(self.allWorkers, self.allBatchSizes):
            self._plotSingle_workers_batchSize(workers, batchSize);

        # Create single plots for each (changeRatio, workers) pair
        for changeRatio, workers in itertools.product(self.allChangeRatios, self.allWorkers):
            self._plotSingle_changeRatio_workers(changeRatio, workers)

        # Create single plots for each (changeRatio, batchSize) pair
        for changeRatio, batchSize in itertools.product(self.allChangeRatios, self.allBatchSizes):
            self._plotSingle_changeRatio_batchSize(changeRatio, batchSize)

        # Create plots for combined workers per changeRatio
        # Fix changeRatio and workers, combine all batchSizes
        for changeRatio in self.allChangeRatios:
            count = 0
            figure1, axis1 = self._plotMultipleInit()
            figure2, axis2 = self._plotMultipleInit()
            for workers in self.allWorkers:
                self._plotMultipleScatter(axis1, changeRatio, workers, "%i workers" % (workers), count)
                self._plotMultipleMedian(axis2, changeRatio, workers, "%i workers" % (workers), count)
                count = count + 1
            self._plotMultipleDoneMedian(figure2, axis2, self._outputFileName("changeRatio", changeRatio, "median-latency", "pdf"))
            self._plotMultipleDoneScatter(figure1, axis1, self._outputFileName("changeRatio", changeRatio, "scatter-latency", "pdf"))

        # Create plots for combined changeRatio per worker
        # Fix worker and changeRatio, combine all batchSizes
        for worker in self.allWorkers:
            count = 0
            figure, axis = self._plotMultipleInit()
            for changeRatio in self.allChangeRatios:
                self._plotMultipleScatter(axis, changeRatio, worker, 'Change ratio %i%%' % (changeRatio), count)
                count = count + 1
            self._plotMultipleDoneScatter(figure, axis, self._outputFileName("worker", worker, "scatter-combined", "pdf"))

class Combined():

    def __init__(self, analysis, **kwargs):
        self.analysis = analysis

    def collectLatency(self, ana, changeRatios, workers, batchSizes):
        try:
            dataObjs = [ ana._groupedData[Index(changeRatio, worker, batchSize)]
                        for changeRatio, worker, batchSize in itertools.product(changeRatios, workers, batchSizes) ]
        except KeyError, e:
            print(e)
            print(ana.staticConfig)
            print(ana._groupedData.keys())
            raise e
        latency = [ d.incrementalMedian for d in dataObjs ]
        return latency, numpy.std([ d.incrementalArray for d in dataObjs], axis=1), dataObjs

    def plot1(self, names):
#         workers = [1, 8, 16, 32]
        changes = [ 20 ]
        batchSize = [ 32 ]
        workers = [1, 8, 16, 32]
        data = []
        stds = []
        for ana in self.analysis:
            d, std = self.collectLatency(ana, changes, workers, batchSize)
            data.append(d)
            stds.append(std)

        print data

        N = len(changes) * len(batchSize) * len(workers)
        ind = numpy.arange(N)
        width = 0.35
        with PdfPages(self.analysis[0]._outputFileName("barchart", 'batchSize', batchSize[0], 'changes', changes[0], "workers-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            for ana, d, std, i in zip(self.analysis, data, stds, itertools.count()):
                bar = ax.bar(ind + i * width, d, width, label=names[i], yerr=std)
                autolabel(bar, ax)
            ax.set_xlabel('Number of workers')
            ax.set_xticks(ind + width / 2)
            ax.set_xticklabels(workers)
            start, end = ax.get_ylim()
            ax.yaxis.set_ticks(numpy.arange(start, end, 50))
            ax.axhline(50, color='b', linestyle='dotted', linewidth=1)
            ax.legend()
 
            pdf.savefig(bbox_inches='tight')
            plt.close()

    def plot2(self, names): #, amadeus):
#         workers = [1, 8, 16, 32]
        changes = [ 40 ]
        batchSize = [ 16 ]
        workers = [1, 2, 4, 8, 16, 32]
        data = []
        stds = []
        for ana in self.analysis:
            d, std, _ = self.collectLatency(ana, changes, workers, batchSize)
            d = d / d[0]
            data.append(d)
            stds.append(std)

        # handle amadeus
#        d, std, _ = self.collectLatency(amadeus, [ 1 ], workers, [ 1 ])
#        d = d / d[0]
#        data.append(d)
#        stds.append(std)

        print data

        N = len(changes) * len(batchSize) * len(workers)
        ind = numpy.arange(N)
        width = 0.18
        with PdfPages(self.analysis[0]._outputFileName("barchart", 'batchSize', batchSize[0], 'changes', changes[0], "workers-latency-normalized", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            for d, std, i in zip(data, stds, itertools.count()):
                bar = ax.bar(ind + i * width, d, width, label=names[i])
                autolabel(bar, ax, f=(lambda x: '%.1f' % x))
            ax.set_xlabel('Workers')
            ax.set_ylabel('Latency (normalized)')
            ax.set_xticks(ind + len(self.analysis) * width / 3)
            ax.set_xticklabels(workers)
#             start, end = ax.get_ylim()
#             ax.yaxis.set_ticks(numpy.arange(start, end, 50))
#             ax.axhline(50, color='b', linestyle='dotted', linewidth=1)
            ax.legend()
 
            pdf.savefig(bbox_inches='tight')
            plt.close()

    def plot3(self, batchSize, names):
        print batchSize
#         workers = [1, 8, 16, 32]
        #batchSize = [ 16, 512 ] # x < y!
        names = [ '%s B=%d' % (names[0], batchSize[0]),
                  '%s B=%d' % (names[1], batchSize[0]),
                  '%s B=%d' % (names[0], batchSize[1]),
                  '%s B=%d' % (names[1], batchSize[1])]
        changes = self.analysis[0].allChangeRatios
        workers = [ 8 ]
        data = []
        stds = []
        analysis = self.analysis[:2]
        for ana in analysis:
            d, std, _ = self.collectLatency(ana, changes, workers, [ batchSize[0] ])
            data.append(d)
            stds.append(std)
        for ana in analysis:
            d, std, _ = self.collectLatency(ana, changes, workers, [ batchSize[1] ])
            d = numpy.array(d) / batchSize[1] * batchSize[0]
            data.append(d)
            stds.append(std)

        print data

        with PdfPages(self.analysis[0]._outputFileName("chart", 'workers', workers[0], 'batchSize', batchSize[0], 'batchSize', batchSize[1], "changes_latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            for ana, d, std, i in zip(itertools.cycle(analysis), data, stds, itertools.count()):
                ax.scatter(xrange(len(d)), d, marker=Plotter.MARKERS[i], label=names[i])
            ax.set_xlabel('Weight change [\%]')
            ax.set_ylabel('Median latency [ms] per batch element')
            ax.set_xticks(range(len(self.analysis[0].allChangeRatios)))
            ax.set_xticklabels(self.analysis[0].allChangeRatios)
#             start, end = ax.get_ylim()
#             ax.yaxis.set_ticks(numpy.arange(start, end, 50))
#             ax.axhline(50, color='b', linestyle='dotted', linewidth=1)
            ax.legend()
 
            pdf.savefig(bbox_inches='tight')
            plt.close()

    def plot4(self, names):
#         workers = [1, 8, 16, 32]
        names = [ '%s B=1' % names[0],  '%s B=1' % names[1],
                  '%s B=8' % names[0],  '%s B=8' % names[1]]
        changes = self.analysis[0].allChangeRatios
        workers = [ 8 ]
        data = []
        stds = []
        for ana in self.analysis:
            d, std = self.collectLatency(ana, changes, workers, [ 1 ])
            data.append(d)
            stds.append(std)
        for ana in self.analysis:
            d, std = self.collectLatency(ana, changes, workers, [ 8 ])
            d = numpy.array(d) / 8
            data.append(d)
            stds.append(std)

        print data

        with PdfPages(self.analysis[0]._outputFileName("chart", 'workers', 8, 'batchSize', 1, 'batchSize', 8, "changes_latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            for ana, d, std, i in zip(itertools.cycle(self.analysis), data, stds, itertools.count()):
                ax.scatter(xrange(len(d)), d, marker=Plotter.MARKERS[i], label=names[i])
            ax.set_xlabel('Weight change [%]')
            ax.set_ylabel('Median latency [ms] per batch element')
            ax.set_xticks(range(len(self.analysis[0].allChangeRatios)))
            ax.set_xticklabels(self.analysis[0].allChangeRatios)
#             start, end = ax.get_ylim()
#             ax.yaxis.set_ticks(numpy.arange(start, end, 50))
#             ax.axhline(50, color='b', linestyle='dotted', linewidth=1)
            ax.legend()
 
            pdf.savefig(bbox_inches='tight')
            plt.close()

    def plot5(self, names):
#         workers = [1, 8, 16, 32]
        changes = [ [ 1 ], [ 1 ], [ 1 ] ]
        batchSize = [ 1 ]
        workers = [1, 8, 16, 32]
        data = []
        stds = []
        raw = []
        for ana, c in zip(self.analysis, changes):
            d, std, r = self.collectLatency(ana, c, workers, batchSize)
            data.append(d)
            stds.append(std)
            raw.append(r)
            print(std)

        print data

        N = 1 * len(batchSize) * len(workers)
        ind = numpy.arange(N)
        width = 0.2
        with PdfPages(self.analysis[0]._outputFileName("update_failure_barchart", 'batchSize', batchSize[0], "workers-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            cell_text = []
            for ana, d, std, i in zip(self.analysis, data, stds, itertools.count()):
                r = [ x.incrementalArray for x in raw[i]]
                cell_text.append(['%1.1f' % x for x in numpy.percentile(r, 95, 1)])
                bar = ax.bar(ind + i * width, d, width, label=names[i])
                autolabel(bar, ax, f=(lambda x: '%.1f' % x))
#            ax.set_xlabel('Number of workers')
            ax.set_ylabel('Median latency [ms]')
#            ax.set_xticks(ind + width / 2)
            ax.set_xticklabels([])
#             start, end = ax.get_ylim()
#             ax.yaxis.set_ticks(numpy.arange(start, end, 50))
#             ax.axhline(50, color='b', linestyle='dotted', linewidth=1)
            the_table = ax.table(cellText=cell_text,
                      rowLabels=names,
                      colLabels=workers,
                      loc='bottom',
                      fontsize=20)
            table_props = the_table.properties()
            table_cells = table_props['child_artists']
            for cell in table_cells:
                cell.set_height(0.1)
            ax.legend()
 
            pdf.savefig(bbox_inches='tight')
            plt.close()

    def plot6(self, names):
#         workers = [1, 8, 16, 32]
        changes = [ 40 ]
        batchSizes = [ [ 128 ], [ 128 ] ]
        workers = [ 1, 2, 4, 8, 16, 32 ]
        data = []
        for batchSize, ana in zip(batchSizes, self.analysis):
            _, _, dataObjs = self.collectLatency(ana, changes, workers, batchSize)
            data.append(dataObjs)

        print data

        with PdfPages(self.analysis[0]._outputFileName("scatter", 'workers', workers[0], 'changes', changes[0], "throughput-latency", "pdf")) as pdf:
            fig = plt.figure()
            ax = fig.add_subplot(1,1,1)
            sign = -1
            for dataObjs, i in zip(data, itertools.count()):
                ax.scatter([ d.throughput for d in dataObjs], [ d.incrementalMedian for d in dataObjs],
                           label=names[i])
                for d, w in zip(dataObjs, workers):
                    ax.text(d.throughput + sign*30 - 15, d.incrementalMedian+sign*100 - 100, w)
                sign = -1 * sign
            ax.set_xlabel('Throughput [updates/s]')
            ax.set_ylabel('Median update latency [ms]')
            ax.legend()
 
            pdf.savefig(bbox_inches='tight')
            plt.close()

class Export(Analysis):
    def __init__(self, name, staticConfig, args):
        super(Export, self).__init__(name, staticConfig, args)

    def export(self):
        converted = {}
        for config, data in self.data.iteritems():
            idx = Index(config.changeRatio, config.workers, config.batchSize)
            secondary = converted.get(idx, {})
            secondary[config.batchSize] = data
            converted[idx] = secondary

        for idx in converted:
            data = converted[idx]
            for batchSize in data:
                values = data[batchSize]
                with open(self._outputFileName(idx, str(batchSize), "cvs"), 'wb') as f:
                    for value in values.incremental:
                        f.write(str(value))
                        f.write('\n')

if __name__ == '__main__':

    configs = {
        # hosts switches ports
        ('small', 'jellyfish') : (8192, 390, 32),
        ('small', 'fat-tree') : (8192, 1280, 32),
        ('large', 'jellyfish') : (27648, 864, 48),
        ('large', 'fat-tree') : (27648, 2880, 48),
        ('small', 'amadeus') : (0, 1000, 32),
    }

    def createConfig(args):
        (hosts, switches, ports) = configs[(args.size, args.topology)]
        return StaticConfiguration(args.topology, 'pgql', 'pgql', switches, ports, hosts, args.batches, args.prefix)

    def run(args, staticConfig):
        rb = RunBenchmark(staticConfig, args)
        rb.doBenchmarks()

    def plot(args, staticConfig):
        plotter = Plotter(staticConfig.getDirName() + '/plot/', staticConfig, args)
        plotter.plot()

    def export(args, staticConfig):
        export = Export(staticConfig.getDirName() + '/export/', staticConfig, args)
        export.export()

    def combined(args, staticConfig):
        analysis = []
        print("Reading data...")
        args.size = 'small'
        args.topology = 'jellyfish'
        staticConfig = createConfig(args)
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args.topology = 'fat-tree'
        staticConfig = createConfig(args)
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args.topology = 'jellyfish'
        args.size = 'large'
        staticConfig = createConfig(args)
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args.topology = 'fat-tree'
        args.size = 'large'
        staticConfig = createConfig(args)
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args = argparse.Namespace(**args.__dict__)
        args.topology = 'amadeus'
        args.size = 'small'
#        args.batches = 100
#        args.maxBatchSize = 1
        staticConfig = createConfig(args)
#        staticConfig.binary = 'linkfailure'
#        args.changeRatios = [ 1 ]
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
#        p = Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args)
#        p._convertData()
        print("Plotting data...")
        map(Plotter._convertData, analysis)
        combined = Combined(analysis)
        names = ['Jellyfish small', 'Fat-tree small', 'Jellyfish large', 'Fat-tree large', 'Topo-R']
        combined.plot2(names)
        return
        for i, batchSize1 in enumerate(analysis[0].allBatchSizes[:-1]):
            for batchSize2 in analysis[0].allBatchSizes[i+1:]:
                combined.plot3([batchSize1, batchSize2], names)

    def plotUpdateFailure(args, staticConfig):
        args.maxBatchSize = 1
        analysis = []
        print("Reading data...")
#        args.size = 'small'
#        args.topology = 'jellyfish'
#        staticConfig = createConfig(args)
#        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
#        args = argparse.Namespace(**args.__dict__)
#        args.topology = 'fat-tree'
#        staticConfig = createConfig(args)
#        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
#        args = argparse.Namespace(**args.__dict__)
        args.batches = 100
        args.size = 'small'
        args.changeRatios = [ 1 ]
        args.topology = 'jellyfish'
        staticConfig = createConfig(args)
        staticConfig.binary = 'linkfailure'
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args = argparse.Namespace(**args.__dict__)
        args.topology = 'fat-tree'
        staticConfig = createConfig(args)
        staticConfig.binary = 'linkfailure'
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args = argparse.Namespace(**args.__dict__)
        args.topology = 'amadeus'
        staticConfig = createConfig(args)
        staticConfig.binary = 'linkfailure'
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
#        tmp = analysis[1]
#        analysis[1] = analysis[2]
#        analysis[2] = tmp
#         args.topology = 'jellyfish'
#         args.size = 'large'
#         staticConfig = createConfig(args)
#         analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
#         args.topology = 'fat-tree'
#         args.size = 'large'
#         staticConfig = createConfig(args)
#         analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        print("Plotting data...")
        map(Plotter._convertData, analysis)
        combined = Combined(analysis)
        combined.plot5(names=['Jellyfish', 'Fat-tree', 'Topo-R'])

    def plotCombinedThroughput(args, staticConfig):
        analysis = []
        print("Reading data...")
        args.size = 'small'
        args.topology = 'jellyfish'
        staticConfig = createConfig(args)
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        args.size = 'small'
        args.topology = 'fat-tree'
        staticConfig = createConfig(args)
        analysis.append(Plotter(staticConfig.getDirName() + '/plot_combined', staticConfig, args))
        print("Plotting data...")
        map(Plotter._convertData, analysis)
        combined = Combined(analysis)
        combined.plot6(names=['Jellyfish', 'Fat-tree'])

    parser = argparse.ArgumentParser(description="Benchmark tool")
    choices = { f.__name__ : f for f in [run, plot, export, combined, plotUpdateFailure, plotCombinedThroughput]}
    parser.add_argument('action', choices=choices)

    parser.add_argument('--prefix', help='data prefix', default=socket.gethostname())
    parser.add_argument('--topology', choices=['jellyfish', 'fat-tree', 'amadeus'], default='jellyfish')
    parser.add_argument('--size', choices=['small', 'large'], default='small')
    parser.add_argument('--batches', type=int, default=300)
    parser.add_argument('--max-workers', type=int, default=multiprocessing.cpu_count(), dest='maxWorkers')
    parser.add_argument('--max-batch', type=int, default=512, dest='maxBatchSize')
    parser.add_argument('--changes', nargs='+', type=int, choices=xrange(1,99),
                        dest='changeRatios', default=[5, 10, 20, 40, 60, 80])

    args = parser.parse_args()
    staticConfig = createConfig(args)
    choices[args.action](args, staticConfig)
