function assert(condition, message) {
    if (!condition) {
        alert("Assertion failed: " + message);
        throw message || "Assertion failed";
    }
}
