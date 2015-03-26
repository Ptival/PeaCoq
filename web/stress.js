function stress() {
    // fake loading some file
    onLoad(
        " \
Ltac ackerman m n := \
match m with \
| O => constr:(S n) \
| S ?m' => \
match n with \
| O => \
let res := ackerman m' 1 in \
constr:(res) \
| S ?n' => \
let tmp1 := ackerman m n' in \
let tmp2 := ackerman m' tmp1 in \
constr:(tmp2) \
end \
end. \
Theorem t (n:nat) (m:nat) (H: n + m = 42) : False. \
Proof. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
let res := ackerman 3 5 in pose res. \
Admitted. \
"
    );

    var times = [];

    function waitThenAct() {
        return delayPromise(1000)()
            .then(function() {
                var after = new Date();
                var diff = after - before;
                console.log(before, after, diff);
                times.push(diff);
                return onCtrlDown(true);
            })
        ;
    }

    // could have been a _.reduce if I cared...
    var before = new Date();
    onCtrlDown(true)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(waitThenAct)
        .then(function() {
            console.log(times);
        })
    ;

}
