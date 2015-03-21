var processingAsync = false; // TODO: scope this
var asyncRequests = [];

function delayPromise(time) {
    return function(result) {
        return new Promise(function(onFulfilled, onRejected) {
            window.setTimeout(function() { onFulfilled(result); }, time);
        });
    }
}

/*
  This is the only function which does not return a promise. It is not to be
  called directly, use one of the async* methods below.
*/
function processAsyncRequests() {

    //console.log("------------------------------------------------------");
    //console.log("TRYING TO PROCESS");

    if (processingAsync) {
        //console.log("NOT PROCESSING BECAUSE WE ARE ALREADY PROCESSING");
        return;
    }

    if (_(asyncRequests).isEmpty()) {
        //console.log("NO MORE REQUESTS TO PROCESS");
        return;
    }

    var request = asyncRequests.shift();
    var r = request.url;
    var q = request.query;
    var h = request.callback;
    if (r === 'query') { console.log(q); }
    processingAsync = true;
    //console.log("+ LOCKING");
    //console.log("TRIGGERING", r, q);
    editorOnRequestTriggered(r, q);
    var beforeTime = Date.now();
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: true,
        error: function() {
            processingAsync = false;
            alert("Server did not respond!");
        },
        success: function(response) {
            var response = new Response(response);

            var afterTime = Date.now();
            processingAsync = false;
            //console.log("- UNLOCKING");
            //console.log("RESPONDING", r, q, response);

            //TODO: the next things should be then-chained so that they happen
            //in the correct order, unless they are fully synchronous

            editorOnResponse(r, q, response);
            if (activeProofTree !== undefined) {
                activeProofTree.onResponse(r, q, response);
            }

            // looks like we should keep processing regardless
            processAsyncRequests();

            /*
            switch (response.rResponse.tag) {
            case 'Good':
                // start processing the next request
                processAsyncRequests();
                break;
            case 'Fail':
                // THIS SEEMS LIKE A BAD IDEA AS IT FLUSHES VALID COMMANDS WHEN
                // QUERYUNDOES FAIL
                // flush all further requests
                // console.log(r, q, "failed, flushing async requests");
                // asyncRequests = [];
                break;
            }
            */

            h(response);

        }
    });
}

/*
 *  @return {Promise}
 */
function asyncRequest(r, q) {
    //console.log("ASYNCREQUEST", r, q);
    // so far, no need for activeProofTree.onRequest
    return new Promise(function(onFulfilled, onRejected) {

        //console.log("QUEUEING", r, q);
        asyncRequests.push({
            "url": r,
            "query": q,
            "callback": onFulfilled,
        });

        processAsyncRequests();
    });
}

/*
 *  @return {Promise}
 */
function asyncQuery(q)        { return asyncRequest('query', q); }
function asyncQueryAndUndo(q) { return asyncRequest('queryundo', q); }
function asyncUndo()          { return asyncRequest('undo', ''); }
function asyncRevision()      { return asyncRequest('revision', ''); }
function asyncRewind(delta) {
    console.log('Rewind', delta);
    return asyncRequest('rewind', delta);
}
function asyncLog(s) {
    var time = "[" + new Date().toLocaleString() + "] ";
    return asyncRequest("log", time + s);
}
/*
function asyncParse(q)       { return asyncRequest('parse', q); }
function asyncParseEval(q)   { return asyncRequest('parseEval', q); }
function asyncParseCheck(q)  { return asyncRequest('parseCheck', q); }
function asyncListLectures() { return asyncRequest("listLectures", ""); }
function asyncLoadLecture(q) { return asyncRequest("loadLecture", q); }
*/

/*
 *  @return {Promise}
 */
function asyncStatus() {
    return asyncRequest("status", "").then(function(response) {
        var msg = response.rResponse.contents[0];
        var r = msg.match("^\\\((.*),(.*),(.*),\"(.*)\",\"(.*)\"\\\)$");
        var result = {
            "sections": r[1],
            "current": (r[2] === "Nothing")
                ? null
                : r[2].substring(5).replace(/"/g, ""),
            "currents": r[3],
            "label": + r[4],
            "proving": (r[5] === "1"),
            "response": response,
        };
        return result;
    });
}

/*
 *  @return {Promise}
 */
function asyncCurrentLabel() {
    return asyncStatus()
        .then(function(status) { return status.label; })
    ;
}

/*
 *  @return {Promise}
 */
function asyncResetCoq() {
    return asyncCurrentLabel()
        .then(function(label) {
            if (label > 0) {
                return asyncRewind(label - 1);
            } else {
                return Promise.resolve();
            }
        });
}

function makeGoals(list) {
    return _(list)
        .map(function(elt) {
            return new Goal(elt);
        })
        .value()
    ;
}

function Response(response) {
    this.response = response.rResponse;

    this.focused = makeGoals(response.rGoals.focused);

    this.unfocused = _(response.rGoals.unfocused)
        .map(function(elt) {
            var goalsBefore = elt[0];
            var goalsAfter  = elt[1];

            return {
                "goalsBefore": makeGoals(goalsBefore),
                "goalsAfter": makeGoals(goalsAfter),
            };
        })
        .value()
    ;

    // TO REMOVE
    this.rGoals = response.rGoals;
    this.rResponse = response.rResponse;
}

function listToString(list, eltToString) {
    return (
        "["
            + _(list).reduce(function(acc, elt, ndx) {
                return acc + ((ndx > 0) ? ", " : "") + eltToString(elt);
            }, "")
            + "]"
    );
}

Response.prototype.toString = function() {
    return (
        "{"
            + "\nfocused: "
            + listToString(
                this.focused,
                function(elt) { return elt.toString(); }
            )
            + "\nunfocused: "
            + listToString(
                this.unfocused,
                function(elt) {
                    return (
                        "("
                            + listToString(
                                elt.goalsBefore,
                                function(elt) { return elt.toString(); }
                            )
                            + ", "
                            + listToString(
                                elt.goalsAfter,
                                function(elt) { return elt.toString(); }
                            )
                            + ")"
                    );
                }
            )
            + "\nresponse: " + JSON.stringify(this.response)
            + "\n}"
    );
}

function Goal(g) {
    this.gId = g.gId;
    this.gHyps = g.gHyps;
    this.gGoal = g.gGoal;
}

Goal.prototype.toString = function() {
    return this.gId; //showTermText(extractGoal(this.gGoal));
}
