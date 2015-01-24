#!/usr/bin/env python
from __future__ import print_function

import csv, sys, os.path
from datetime import datetime
from boomslang import *

def usage():
    print('Usage: graph.py data.csv')

class Entry:
    def __init__(self, ver, stm, ctm, cmd, pay):
        self.version = ver
        self.serverT = stm
        self.clientT = ctm
        self.command = cmd
        self.payload = pay

    def __repr__(self):
        return '''
Entry( version: %s
     , serverT: %s
     , clientT: %s
     , command: %s
     , payload: "%s"
     )''' % ( self.version
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
            ver = row[0]
            stm = datetime.strptime(row[1], '%Y-%m-%d-%H-%M-%S-%f')
            try:
                ctm = datetime.strptime(row[2], '%Y-%m-%d-%H-%M-%S-%f')
            except:
                ctm = None
            cmd = row[3]
            pay = row[4]
            log.append(Entry(ver, stm, ctm, cmd, pay))

    print(log)

main()
sys.exit(0)

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
