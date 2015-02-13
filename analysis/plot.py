#!/usr/bin/env python2
from __future__ import print_function

import csv, sys, os.path
from datetime import datetime
from boomslang import *

def usage():
    print('Usage: plot.py data.csv')

class Entry:
    def __init__(self, usr, ver, stm, ctm, cmd, pay):
        self.username = usr
        self.version = ver
        self.serverT = stm
        self.clientT = ctm
        self.command = cmd
        self.payload = pay

    def __repr__(self):
        return '''
Entry( username: %s
     , version: %s
     , serverT: %s
     , clientT: %s
     , command: %s
     , payload: "%s"
     )''' % ( self.username
            , self.version
            , self.serverT
            , self.clientT
            , self.command
            , self.payload
            )

    def __str__(self):
        return self.repr()

def main():
    if len(sys.argv) < 2:
        usage()
        sys.exit(1)

    path = sys.argv[1]
    if not os.path.isfile(path):
        print('Error: "%s" does not exist.' % path, file=sys.stderr)
        sys.exit(1)

    with open(path, 'rb') as f:
        log = []
        for row in csv.reader(f):
            usr = row[0]
            ver = row[1]
            stm = datetime.strptime(row[2], '%Y-%m-%d-%H-%M-%S-%f')
            try:
                ctm = datetime.strptime(row[3], '%Y-%m-%d-%H-%M-%S-%f')
            except:
                ctm = None
            cmd = row[4]
            pay = row[5]
            log.append(Entry(usr, ver, stm, ctm, cmd, pay))

    # commands per day
    cmdSum = {}
    for l in log:
        d = l.serverT.strftime('%y-%m-%d')
        if not (d in cmdSum):
            cmdSum[d] = 0
        cmdSum[d] += 1

    plot = Plot()
    line = Line()
    line.xValues = []
    line.yValues = []
    labs = []

    n = 1
    for d in sorted(cmdSum.keys()):
        line.xValues.append(n)
        line.yValues.append(cmdSum[d])
        labs.append(d)
        n += 1

    labpos = [(i * n) / 10 for i in range(10)]
    line.xTickLabels = [labs[i] for i in labpos]
    line.xTickLabelPoints = labpos

    line.xTickLabelProperties = {
        "color" : "blue",
        "rotation" : 30,
        "fontsize" : 9
    }
    plot.yLabel = "Total Commands"
    plot.add(line)
    plot.setDimensions(9,6)
    plot.save("cmds-by-day.png")


if __name__ == '__main__':
    main()

x = '''

    # commands per day
    plot = Plot()
    line = Line()

    tlabs = []
    line.xValues = []
    line.yValues = []

    n = 1
    for e in log:
        tlabs.append(e.clientT)
        line.xValues.append(n)
        line.yValues.append(int(row[1]))
        n += 1

      tpts = [(i * n) / 10 for i in range(10)]
      line.xTickLabels = [tlabs[i] for i in tpts]
      line.xTickLabelPoints = tpts

    line.xTickLabelProperties = {
        "color" : "blue",
        "rotation" : 30,
        "fontsize" : 9
    }
    plot.yLabel = "Diff Size"
    plot.add(line)
    plot.setDimensions(9,6)
    plot.save("time-diffs.png")




# commands per day
plot = Plot()
line = Line()

tlabs = []
line.xValues = []
line.yValues = []
with open('counts.csv', 'rb') as f:
  n = 1
  for row in csv.reader(f):
    tlabs.append(row[0])
    line.xValues.append(n)
    line.yValues.append(int(row[1]))
    n += 1

  tpts = [(i * n) / 10 for i in range(10)]
  line.xTickLabels = [tlabs[i] for i in tpts]
  line.xTickLabelPoints = tpts

line.xTickLabelProperties = {
    "color" : "blue",
    "rotation" : 30,
    "fontsize" : 9
}
plot.yLabel = "Diff Size"
plot.add(line)
plot.setDimensions(9,6)
plot.save("time-diffs.png")

# day
plot = Plot()
bar = Bar()

day  = [ 0 for i in range(7)]
nday = [ 0 for i in range(7)]

with open('counts.csv', 'rb') as f:
  for row in csv.reader(f):
    d = time.strptime(row[0], "%Y-%m-%d %H:%M:%S")
    day[d.tm_wday] += int(row[1])
    nday[d.tm_wday] += 1

  bar.xValues = range(7)
  bar.yValues = [float(day[i]) / float(nday[i]) for i in range(7)]
  bar.xTickLabels = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

bar.color = "green"
bar.xTickLabelProperties = {
    "color" : "blue",
    "fontsize" : 12
}
plot.xLimits = (-1, 7)
plot.yLabel = "Avg Diff Size"
plot.add(bar)
plot.setDimensions(9,4)
plot.save("day-diffs.png")


# hour
plot = Plot()
bar = Bar()

hour  = [0 for i in range(24)]
nhour = [0 for i in range(24)]

with open('counts.csv', 'rb') as f:
  for row in csv.reader(f):
    d = time.strptime(row[0], "%Y-%m-%d %H:%M:%S")
    hour[d.tm_hour] += int(row[1])
    nhour[d.tm_hour] += 1

  bar.xValues = range(24)
  bar.yValues = [float(hour[i]) / float(nhour[i]) if nhour[i] != 0 else 0 for i in range(24)]
  bar.xTickLabelPoints = [0, 3, 6, 9, 12, 15, 18, 21]
  bar.xTickLabels = ["12am", "3am", "6am", "9am", "12pm", "3pm", "6pm", "9pm"]

bar.color = "red"
bar.xTickLabelProperties = {
    "color" : "blue",
    "fontsize" : 12
}
plot.xLimits = (-1, 24)
plot.yLabel = "Avg Diff Size"
plot.add(bar)
plot.setDimensions(9,4)
'''
