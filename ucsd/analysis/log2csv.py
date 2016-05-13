#!/usr/bin/env python3

import os, sys, io, re, csv

from os.path import basename, splitext
from glob import glob

# hacky: find whenever there is a newline followed by "[2015" or the EOF
rItem = re.compile(r'\n(?=\[201)')

# [2015-11-26 01:23:45 PST]
rServerDate = r'\[(\d+)-(\d+)-(\d+) (\d+):(\d+):(\d+) P[DS]T\]'
# [26/11/2015, 1:23:45 AM]
rClientDate = r'\[(\d+)\/(\d+)\/(\d+), (\d+):(\d+):(\d+) (AM|PM)\]'

rHash = "(\d{40})"

rCommand = r'(\w*)'
rPayload = r'([\s\S]*)'

# new format
r4 = re.compile('^' + rServerDate + ' ' + rHash + ' ' + rClientDate + ' ' + rCommand + rPayload + '$')
r3 = re.compile('^' + rServerDate + ' ' + rHash + ' ' + rCommand + rPayload + '$')
# old format
r2 = re.compile('^' + rServerDate + ' ' + rClientDate + ' ' + rCommand + rPayload + '$')
r1 = re.compile('^' + rServerDate + ' ' + rCommand + rPayload + '$')

def adjust(hour, ampm):
    if ampm == "PM":
        return int(hour) + 12
    else:
        return int(hour)

if __name__ == '__main__':
    home = os.getenv('HOME')
    mode = 'w'
    if sys.version_info.major < 3:
        mode += 'b'
    with io.open(home + '/PeaCoq/logs/data.csv', mode) as csvfile:
        writer = csv.writer(csvfile)
        # long format to make sure we don't open status and error logs
        for file in glob(home + '/PeaCoq/logs/*-*-*-*-*-*-*.log'):
            if 'error' in file: continue
            if 'access' in file: continue
            (root, ext) = splitext(file)
            userFilename = basename(file).split('-')[0]
            with open(file) as handle:
              filetext = handle.read()
              items = rItem.split(filetext)
              for item in items:
                  if item == "":
                      continue
                  # there has got to be a better way to do this :(

                  print('.', end='')

                  # we don't record this
                  user = userFilename

                  m = r4.match(item)
                  if m:
                      args = [ int(m.group(i)) for i in range(1, 7) ]
                      serverdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}-000".format(*args)
                      version = m.group(7)
                      args = list(map(lambda x: int(x), (m.group(10), m.group(8), m.group(9), adjust(m.group(11), m.group(14)), m.group(12), m.group(13))))
                      clientdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}-000".format(*args)
                      command = m.group(15)
                      payload = m.group(16)
                      writer.writerow([user, version, serverdate, clientdate, command, payload])
                      continue

                  m = r3.match(item)
                  if m:
                      args = list(map(lambda x: int(x), (m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), m.group(6))))
                      serverdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}-000".format(*args)
                      version = m.group(7)
                      clientdate = ""
                      command = m.group(8)
                      payload = m.group(9)
                      writer.writerow([user, version, serverdate, clientdate, command, payload])
                      continue

                  # we used not to record this
                  version = "0000000000000000000000000000000000000000"

                  m = r2.match(item)
                  if m:
                      args = list(map(lambda x: int(x), (m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), m.group(6))))
                      serverdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}-000".format(*args)
                      args = list(map(lambda x: int(x), (m.group(9), m.group(7), m.group(8), adjust(m.group(10), m.group(13)), m.group(11), m.group(12))))
                      clientdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}-000".format(*args)
                      command = m.group(14)
                      payload = m.group(15)
                      writer.writerow([user, version, serverdate, clientdate, command, payload])
                      continue

                  m = r1.match(item)
                  if m:
                      args = list(map(lambda x: int(x), (m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), m.group(6))))
                      serverdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}-000".format(*args)
                      clientdate = ""
                      command = m.group(7)
                      payload = m.group(8)
                      writer.writerow([user, version, serverdate, clientdate, command, payload])
                      continue

                  print('FAILED', item)
                  exit(0)
