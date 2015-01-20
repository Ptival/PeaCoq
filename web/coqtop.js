var processingAsync = false; // TODO: scope this
var asyncRequests = [];

/*
  This is the only function which does not return a promise. It is not to be
  called directly, use one of the async* methods below.
*/
function processAsyncRequests() {
    if (processingAsync || _(asyncRequests).isEmpty()) { return; }
    var request = asyncRequests.shift();
    var r = request.url;
    var q = request.query;
    var h = request.callback;
    if (r === 'query') { console.log(q); }
    processingAsync = true;
    var beforeTime = Date.now();
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: true,
        success: function(response) {
            var afterTime = Date.now();
            processingAsync = false;
            processAsyncRequests();
            h(response);
        }
    });
}

/*
 *  @return {Promise}
 */
function asyncRequest(r, q) {
    return new Promise(function(onFulfilled, onRejected) {
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
function asyncUndo()          { return asyncRequest('undo', undefined); }
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
                return asyncRequest("rewind", label - 1)
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
                return asyncRequest("rewind", label - 1);
            } else {
                return Promise.resolve();
            }
        });
}
