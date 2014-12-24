#!/usr/bin/env python

import glob

for fn in glob.glob('*.html'):
    with open(fn, 'r') as f:
        h = f.read()
    h = h.replace('coqdoc.css', 'coqdoc-505.css')
    with open(fn, 'w') as f:
        f.write(h)
