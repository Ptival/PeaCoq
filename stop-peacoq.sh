#!/usr/bin/env bash

USERNAME=$(whoami)

killall -u $USERNAME peacoq &> /dev/null
