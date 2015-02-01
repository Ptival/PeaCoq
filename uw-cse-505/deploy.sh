#!/usr/bin/env bash

set -e
set -x

ssh attu.cs.washington.edu     "\$HOME/PeaCoq/uw-cse-505/update.sh"
ssh tricycle.cs.washington.edu "\$HOME/PeaCoq/uw-cse-505/update.sh"

ssh tricycle.cs.washington.edu "\$HOME/PeaCoq/stop-peacoq.sh || true"

ssh tricycle.cs.washington.edu <<EOF
nohup \$HOME/PeaCoq/start-peacoq.sh bboston7 60160 &>/dev/null &
EOF
ssh tricycle.cs.washington.edu <<EOF
nohup \$HOME/PeaCoq/start-peacoq.sh georgem6 58870 &>/dev/null &
EOF
ssh tricycle.cs.washington.edu <<EOF
nohup \$HOME/PeaCoq/start-peacoq.sh asnchstr 60180 &>/dev/null &
EOF
ssh tricycle.cs.washington.edu <<EOF
nohup \$HOME/PeaCoq/start-peacoq.sh kimyen 58690 &>/dev/null &
EOF
