
function syncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: false,
        success: function(response) {
            //console.log("response", response);
            h(response);
        }
    });
}

function syncQuery(q, h)       { syncRequest('query', q, h); }
function syncQueryUndo(q, h)   { syncRequest('queryundo', q, h); }
function syncUndo(h)           { syncRequest('undo', undefined, h); }
function syncParse(q, h)       { syncRequest('parse', q, h); }
function syncParseEval(q, h)   { syncRequest('parseEval', q, h); }
function syncParseCheck(q, h)  { syncRequest('parseCheck', q, h); }
function syncListLectures(h)   { syncRequest("listLectures", "", h); }
function syncLoadLecture(q, h) { syncRequest("loadLecture", q, h); }
function syncLog(s) {
    var time = "[" + new Date().toLocaleString() + "] ";
    syncRequest("log", time + s, function() {});
}

function syncStatus() {
    var result;
    syncRequest("status", "", function(response) {
        var msg = response.rResponse.contents[0];
        var r = msg.match("^\\\((.*),(.*),(.*),\"(.*)\",\"(.*)\"\\\)$");
        result = {
            "sections": r[1],
            "current": (r[2] === "Nothing") ? null : r[2].substring(5).replace(/"/g, ""),
            "currents": r[3],
            "label": + r[4],
            "proving": (r[5] === "1"),
            "response": response,
        };
    });
    return result;
}

function syncCurrentLabel() {
    return syncStatus().label;
}

function syncResetCoq() {
    var label = syncCurrentLabel();
    if (label > 0) {
        syncRequest("rewind", label - 1, function(){});
        syncQuery("Require Import Unicode.Utf8 Bool Arith List.", function(){});
        syncQuery("Open ListNotations.", function(){});
    }
}

function syncResetCoqNoImports() {
    var label = syncCurrentLabel();
    if (label > 0) {
        syncRequest("rewind", label - 1, function(){});
    }
}

function asyncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: true,
        success: function(response) {
            h(response);
        }
    });
}

function asyncQuery(q, h)        { asyncRequest('query', q, h); }
function asyncQueryAndUndo(q, h) { asyncRequest('queryundo', q, h); }
function asyncUndo(h)            { asyncRequest('undo', undefined, h); }
