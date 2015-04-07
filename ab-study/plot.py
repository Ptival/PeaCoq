#!/usr/bin/env python2
from __future__ import print_function

import csv, sys, os.path, re
from datetime import datetime, timedelta
from boomslang import *


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
            , ('NOT SHOWN' if self.command == 'LOAD' else self.payload)
            )

    def __str__(self):
        return self.__repr__()


def buildLog(f):
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
        entry = Entry(usr, ver, stm, ctm, cmd, pay)
        log.append(entry)
    return log


def buildUserBuckets(log):
    userBuckets = {}
    for l in log:
        if not l.username in userBuckets:
            userBuckets[l.username] = []
        userBuckets[l.username].append(l)
    return userBuckets


theoremRE = re.compile('^[\s\S]*Theorem (\S*) *:[\s\S]*$')

lemmaRE = re.compile('^[\s\S]*Lemma (\S*) *:[\s\S]*$')


def findTheoremName(s):
    match = theoremRE.match(s)
    if not match:
        match = lemmaRE.match(s)
    if not match:
        print(s)
        sys.exit(1)
    return(match.group(1))


exercises = [
    "rev_snoc",
    "rev_involutive",
    "concat_cons_snoc",
    "go_somewhere",
    "B_is_enough",
    "more_facts",
    "A_and_B",
    "snoc_concat_end",
    "rev_distributes_over_concat",
    "map_commutes",
    "map_fusion",
    "fold_snoc",
    "map'_unroll",
    "map_map'",
    "In_cons",
    "In_concat_left",
]


def buildExerciseBucket(userBucket):

    # it's easy to compute the timing here, so I'll do it too...
    exerciseBuckets = {}
    timingBuckets = {}
    timelineBuckets = {}

    # initialize buckets to make things simpler down there
    for u in userBucket:
        exerciseBuckets[u] = {}
        timingBuckets[u] = {}
        timelineBuckets[u] = []
        for e in exercises:
            exerciseBuckets[u][e] = []
            timingBuckets[u][e] = timedelta()

    for user in userBucket:
        currentExercise = None
        for l in userBucket[user]:

            # Find if this is the start of an exercise
            if l.command == 'QUERY' and ("Lemma " in l.payload or "Theorem " in l.payload):
                if currentExercise != None:
                    print("Found beginning without end: " + str(currentExercise) + str(l))
                    sys.exit(1)
                currentExercise = l
                #print("Start of exercise: " + currentExercise + str(l))
                continue

            # Find if this is the end of an exercise (proved)
            if l.command == 'QUERY' and "Qed." in l.payload:
                if currentExercise == None:
                    print("Found end without beginning: " + str(l))
                    sys.exit(1)
                exercise = findTheoremName(currentExercise.payload)
                if exercise in exercises:
                    time = l.serverT - currentExercise.serverT
                    #print(l.username + " solved " + exercise + " in " + str(time))
                    timingBuckets[user][exercise] += time
                    timelineBuckets[user].append([exercise, currentExercise.serverT, l.serverT])
                    #print(l)
                #print("End of exercise: " + str(currentExercise) + str(l))
                currentExercise = None
                continue

            # Find if this is the end of an exercise (aborted)
            if l.command == 'PROVERUP' and ("Lemma " in l.payload or "Theorem " in l.payload):
                if currentExercise != None:
                    theorem = findTheoremName(l.payload)
                    if findTheoremName(currentExercise.payload) != theorem:
                        print ('Exited an exercise that was not last entered: ' + currentExercise + str(l))
                        sys.exit(1)
                    exercise = findTheoremName(currentExercise.payload)
                    if exercise in exercises:
                        time = l.serverT - currentExercise.serverT
                        #print("Gave up on exercise: " + exercise + " after " + str(time))
                        timingBuckets[user][exercise] += time
                        timelineBuckets[user].append([exercise, currentExercise.serverT, l.serverT])
                    currentExercise = None

            # if currentExercise == None:
            #     print("Not an exercise command: " + str(l))
            # else:
            #     print("Exercise command: " + str(l))

    # print(',group1,group2,group3,group4,group5')
    # for e in exercises:
    #     print('%s,%s,%s,%s,%s,%s'
    #           % ( e
    #               , str(timingBuckets['group1'][e])
    #               , str(timingBuckets['group2'][e])
    #               , str(timingBuckets['group3'][e])
    #               , str(timingBuckets['group4'][e])
    #               , str(timingBuckets['group5'][e])
    #           )
    #     )

    for u in ['group1','group2','group3','group4','group5']:
        for l in timelineBuckets[u]:
            e = l[0]
            start = str(l[1])
            end = str(l[2])
            print('%s,%s,%s,%s'
                  % (u, e, start, end))


def main():

    aLog = []
    bLog = []

    with open('a.csv', 'rb') as f:
        aLog = buildLog(f)

    with open('b.csv', 'rb') as f:
        bLog = buildLog(f)

    # these buckets will be used in some functions

    aUserBuckets = buildUserBuckets(aLog)
    bUserBuckets = buildUserBuckets(bLog)

    buildExerciseBucket(bUserBuckets)


def commandsPerDay(log):

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

    if len(labs) > 10:
        labpos = [(i * n) / 10 for i in range(10)]
    else:
        labpos = range(len(labs))
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


def clicksPerUser(userBuckets):

    clicks = {}
    for bucket in userBuckets:
      for l in userBuckets[bucket]:
        if l.command == "CLICK":
          if not (l.username in clicks):
            clicks[l.username] = 0
          clicks[l.username] += 1

    plot = Plot()
    bar = Bar()
    bar.xValues = []
    bar.yValues = []
    labs = []

    n = 1
    for d in sorted(clicks.keys()):
        user = d[:5]
        bar.xValues.append(n)
        bar.yValues.append(clicks[d])
        labs.append(user)
        n += 1

    bar.xTickLabels = labs

    bar.xTickLabelProperties = {
        "color" : "blue",
        "rotation" : 30,
        "fontsize" : 9
    }
    plot.yLabel = "Clicks per user"
    plot.add(bar)
    plot.setDimensions(9,6)
    plot.save("clicks-per-user.png")


def qedsPerUser(userBuckets):

    qeds = {}
    for bucket in userBuckets:
      for l in userBuckets[bucket]:
        if l.command == "QED":
          if not (l.username in qeds):
            qeds[l.username] = 0
          qeds[l.username] += 1

    plot = Plot()
    bar = Bar()
    bar.xValues = []
    bar.yValues = []
    labs = []

    n = 1
    for d in sorted(qeds.keys()):
        user = d[:5]
        bar.xValues.append(n)
        bar.yValues.append(qeds[d])
        labs.append(user)
        n += 1

    bar.xTickLabels = labs

    bar.xTickLabelProperties = {
        "color" : "blue",
        "rotation" : 30,
        "fontsize" : 9
    }
    plot.yLabel = "QEDs per user"
    plot.add(bar)
    plot.setDimensions(9,6)
    plot.save("qeds-per-user.png")


def nbCommands(userBuckets):

    counts = {}
    for bucket in userBuckets:
      counter = 0
      counting = False
      for l in userBuckets[bucket]:
        if counting:
          if l.command == "EXITPROOFTREE" or l.command == "LOAD" or l.command == "NEWSESSION" or l.command == "USERIDENTIFIED" or l.command == "REWIND":
            if not counter in counts:
              counts[counter] = 0
            counts[counter] += 1
            counting = False
          elif l.command == "QUERY":
            continue
          else:
            counter += 1
        else:
          if l.command == "AUTOENTERPROOFTREE":
            counting = True
            counter = 0
          else:
            continue

    bucketSize = 50
    bucketCounts = {}
    del counts[0]
    for count in counts:
      bucketIndex = (count - 1) / bucketSize
      if bucketIndex not in bucketCounts:
        bucketCounts[bucketIndex] = 0
      bucketCounts[bucketIndex] += counts[count]

    plot = Plot()
    bar = Bar()
    bar.xValues = []
    bar.yValues = []
    labs = []

    n = 1
    for d in bucketCounts.keys():
        bar.xValues.append(n)
        bar.yValues.append(bucketCounts[d])
        rangeEnd = ((d + 1) * bucketSize)
        labs.append(str(rangeEnd))
        n += 1

    bar.xTickLabels = labs

    bar.xTickLabelProperties = {
        "color" : "blue",
        "rotation" : 30,
        "fontsize" : 9
    }
    plot.xLabel = "Approximate number of actions"
    plot.add(bar)
    plot.setDimensions(9,6)
    plot.save("actions-per-proof.png")


def nbLefts(userBuckets):

    counts = {}
    for bucket in userBuckets:
      counter = 0
      counting = False
      for l in userBuckets[bucket]:
        if counting:
          if l.command == "EXITPROOFTREE" or l.command == "LOAD" or l.command == "NEWSESSION" or l.command == "USERIDENTIFIED" or l.command == "REWIND":
            if not counter in counts:
              counts[counter] = 0
            counts[counter] += 1
            counting = False
          elif l.command == "LEFT":
            counter += 1
          else:
            continue
        else:
          if l.command == "AUTOENTERPROOFTREE":
            counting = True
            counter = 0
          else:
            continue

    plot = Plot()
    bar = Bar()
    bar.xValues = []
    bar.yValues = []
    labs = []

    n = 1
    for d in sorted(counts.keys()):
        bar.xValues.append(n)
        bar.yValues.append(counts[d])
        labs.append(str(d))
        n += 1

    bar.xTickLabels = labs

    bar.xTickLabelProperties = {
        "color" : "blue",
        "rotation" : 90,
        "fontsize" : 9
    }
    plot.xLabel = "Number of lefts"
    plot.add(bar)
    plot.setDimensions(9,6)
    plot.save("lefts-per-proof.png")



if __name__ == '__main__':
    main()
