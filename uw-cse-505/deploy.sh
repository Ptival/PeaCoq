#!/usr/bin/env bash

ssh attu@cs.washington.edu     "\$HOME/PeaCoq/uw-cse-505/update.sh"
ssh tricycle@cs.washington.edu "\$HOME/PeaCoq/uw-cse-505/update.sh"

ssh tricycle@cs.washington.edu "\$HOME/PeaCoq/start-peacoq.sh bboston7 67960"
ssh tricycle@cs.washington.edu "\$HOME/PeaCoq/start-peacoq.sh georgem6 58870"
ssh tricycle@cs.washington.edu "\$HOME/PeaCoq/start-peacoq.sh asnchstr 67780"
ssh tricycle@cs.washington.edu "\$HOME/PeaCoq/start-peacoq.sh kimyen   58690"
