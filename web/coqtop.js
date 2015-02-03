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
    if (activeProofTree !== undefined) {
        activeProofTree.onRequestTriggered(r, q);
    }
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
            var afterTime = Date.now();
            processingAsync = false;
            //console.log("- UNLOCKING");
            //console.log("RESPONDING", r, q, response);
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
function asyncResetCoqWithImports() {
    return asyncCurrentLabel()
        .then(function(label) {
            if (label > 0) {
                return asyncRewind(label - 1)
                    .then(asyncQuery(
                        "Require Import Unicode.Utf8 Bool Arith List."
                    ))
                    .then(asyncQuery("Open ListNotations."))
                ;
            } else {
                return Promise.resolve();
            }
        })
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
