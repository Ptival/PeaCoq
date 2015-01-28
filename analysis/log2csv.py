#! /usr/bin/env python

import csv
import os
import re

from os.path import splitext
from glob import glob

# hacky: find whenever there is a newline followed by "[2015" or the EOF
rItem = re.compile(r'\n(?=\[201)')

# [2015-11-26 01:23:45 PST]
rServerDate = r'^\[(\d+)-(\d+)-(\d+) (\d+):(\d+):(\d+) PST\]'
# [26/11/2015, 1:23:45 AM]
rClientDate = r'\[(\d+)\/(\d+)\/(\d+), (\d+):(\d+):(\d+) (AM|PM)\]'

rCommand = r'(\w*)'
rPayload = r'([\s\S]*)'

r2 = re.compile('^' + rServerDate + ' ' + rClientDate + ' ' + rCommand + ' ' + rPayload + '$')
r1 = re.compile('^' + rServerDate + ' ' + rCommand + ' ' + rPayload + '$')

def adjust(hour, ampm):
    if ampm == "PM":
        return int(hour) + 12
    else:
        return int(hour)

if __name__ == '__main__':
    home = os.getenv('HOME')
    # long format to make sure we don't open status and error logs
    for file in glob(home + '/PeaCoq/logs/*-*-*-*-*-*-*.log'):
        (root, ext) = splitext(file)
        # TODO: get the username using filename.split('-')[0]
        with open(root + '.csv', 'w', newline='') as csvfile:
            writer = csv.writer(csvfile, dialect='unix')
            filetext = open(file).read()
            items = rItem.split(filetext)
            for item in items:
                if item == "":
                    continue
                m = r2.match(item)
                if m:
                    # ugh Python...
                    args = list(map(lambda x: int(x), (m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), m.group(6))))
                    serverdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}".format(*args)
                    args = list(map(lambda x: int(x), (m.group(9), m.group(7), m.group(8), adjust(m.group(10), m.group(13)), m.group(11), m.group(12))))
                    clientdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}".format(*args)
                    command = m.group(14)
                    payload = m.group(15)
                    print(serverdate, clientdate, command)
                    writer.writerow([serverdate, clientdate, command, payload])
                    continue
                m = r1.match(item)
                if m:
                    args = list(map(lambda x: int(x), (m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), m.group(6))))
                    serverdate = "{:04d}-{:02d}-{:02d}-{:02d}-{:02d}-{:02d}".format(*args)
                    clientdate = "????-??-??-??-??-??"
                    command = m.group(7)
                    payload = m.group(8)
                    print(serverdate, clientdate, command)
                    writer.writerow([serverdate, clientdate, command, payload])
                    continue
                print('FAILED', item)
