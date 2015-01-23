#!/usr/bin/env python
from __future__ import print_function
import os, sys, smtplib
from email.mime.text import MIMEText

def usage():
    print('Usage: feedback.py [path]')

def main():
    if len(sys.argv) < 2:
        usage()
        sys.exit(1)

    path = sys.argv[1]
    if not os.path.isfile(path):
        print('Error: "%s" does not exist.' % path, file=sys.stderr)
        sys.exit(1)

    with open(path, 'rb') as f:
        msg = MIMEText(f.read())

    addr = "vrobert@cs.ucsd.edu"
    msg['Subject'] = 'PeaCoq feedback "%s"' % path
    msg['From'] = addr
    msg['To'] = addr

    s = smtplib.SMTP('smtp.gmail.com')
    s.sendmail(addr, [addr], msg.as_string())
    s.quit()

if __name__ == '__main__':
    main()
