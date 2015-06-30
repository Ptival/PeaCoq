
function coqtop(command, input, callback) {
    $.ajax({
        type: 'POST',
        url: command,
        data: { data: JSON.stringify(input) },
        async: true,
        error: function() {
            console.log("Server did not respond!");
        },
        success: function(response) {
            var result = response[0];
            var messages = response[1][0];
            var feedback = response[1][1];
            console.log("Response: ", response);
            _(feedback).each(function(f) {
                console.log("Feedback: ", new Feedback(f));
            });
            _(messages).each(function(m) {
                console.log("Message: ", new Message(m));
            });
            //console.log("Result: ", result);
            switch (result.tag) {
            case "ValueGood":
                if (callback) { callback(result.contents); }
                break;
            case "ValueFail":
                console.log("Error: ", new ValueFail(result.contents));
                break;
            default:
                throw "result.tag was neither ValueGood nor ValueFail";
            }
        }
    });
}

function peaCoqAddPrime(s) {
    console.log("Add'", s);
    coqtop("add'", s, function(r) {
        var stateId = r[0];
        var eitherNullStateId = r[1][0];
        var output = r[1][1];
        console.log("Initialized, current state Id: ", stateId);
    });
}

function peaCoqInit() {
    console.log("Init");
    coqtop("init", null, function(sid) {
        console.log("Initialized, current state Id: ", sid);
    });
}

function peaCoqQueryPrime(s) {
    console.log("Query'", s);
    coqtop("query'", s, function(r) {
        console.log("Query output: " + r);
    });
}

function ValueFail(v) {
    this.stateId  = v[0];
    this.location = v[1];
    this.message  = v[2];
}

function createMessageLevel(m) {
    switch (m.tag) {
    case "Debug": return new Debug(m.contents);
    case "Error": return new Error();
    case "Info": return new Info();
    case "Notice": return new Notice();
    case "Warning": return new Warning();
    default: throw ("Unknown message level: " + m.tag);
    };
}

function MessageLevel() {
}

function Debug(s) {
    this.debug = s;
    MessageLevel.call(this);
}
Debug.prototype = Object.create(MessageLevel.prototype);
Debug.prototype.constructor = Debug;

function Error() {
    MessageLevel.call(this);
}
Error.prototype = Object.create(MessageLevel.prototype);
Error.prototype.constructor = Error;

function Info() {
    MessageLevel.call(this);
}
Info.prototype = Object.create(MessageLevel.prototype);
Info.prototype.constructor = Info;

function Notice() {
    MessageLevel.call(this);
}
Notice.prototype = Object.create(MessageLevel.prototype);
Notice.prototype.constructor = Notice;

function Warning() {
    MessageLevel.call(this);
}
Warning.prototype = Object.create(MessageLevel.prototype);
Warning.prototype.constructor = Warning;

function Message(m) {
    this.level = createMessageLevel(m[0]);
    this.content = m[1];
}

function Feedback(f) {
    switch (f[0].tag) {
    case "State": this.editOrState = "state"; break;
    case "Edit" : this.editOrState = "edit"; break;
    default: throw "Feedback tag was neither State nor Edit";
    };
    this.editOrStateId = f[0].contents;
    this.feedbackContent = createFeedbackContent(f[1]);
    this.routeId = f[2];
}

function createFeedbackContent(f) {
    this.tag = f.tag;
    switch (this.tag) {
    case "AddedAxiom":
    case "Custom":
    case "ErrorMsg":
    case "FileDependency":
    case "FileLoaded":
    case "GlobDef":
    case "GlobRef":
    case "Goals":
    case "Message":
        alert("TODO: FeedbackContent for " + this.tag);
        break;
    case "Processed": return new Processed();
    case "ProcessingIn":
    case "WorkerStatus":
        alert("TODO: FeedbackContent for " + this.tag);
        break;
        // other tags don't need fields
    default: throw ("Unknown FeedbackContent tag: " + this.tag);
    }
}

function FeedbackContent() {
}

function Processed() {
    FeedbackContent.call(this);
}
Processed.prototype = Object.create(FeedbackContent.prototype);
Processed.prototype.constructor = FeedbackContent;
