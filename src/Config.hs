module Config where

coqtop :: String
--coqtop = "coqtop -ideslave"
--coqtop = "/home/vrobert/.opam/coq-8.4pl6/bin/coqtop -ideslave"
--coqtop = "/home/vrobert/.opam/coq-8.5beta2/bin/coqtop -ideslave -main-channel stdfds"
coqtop = "/home/vrobert/coq-build/bin/coqtop -ideslave -main-channel stdfds"

userId :: String
userId = "default"

logPath :: String
logPath = "/tmp"
