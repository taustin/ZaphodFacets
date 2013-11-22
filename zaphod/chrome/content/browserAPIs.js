/*
 * Narcissus - JS implemented in JS.
 *
 * Browser-specific tweaks needed for Narcissus to execute properly
 */

// Prevent setTimeout from breaking out to SpiderMonkey
Narcissus.interpreter.timeouts=[];
Narcissus.interpreter.global.setTimeout = function(code, delay) {
    var timeoutCode = (typeof code === "string") ?
            function() { Narcissus.interpreter.evaluate(code); } :
            code;
    var tid = setTimeout(timeoutCode, delay);
    Narcissus.interpreter.timeouts.push(tid);
    return tid;
};

// Prevent setInterval from breaking out to SpiderMonkey
Narcissus.interpreter.intervals=[];
Narcissus.interpreter.global.setInterval = function(code, delay) {
    var timeoutCode = (typeof code === "string") ?
            function() { Narcissus.interpreter.evaluate(code); } :
            code;
    var tid = setInterval(timeoutCode, delay);
    Narcissus.interpreter.intervals.push(tid);
    return tid;
};

Zaphod.clearAllTimers = function() {
  // Wipeout setTimeout and setInterval in narcissus so that
  // nothing calls them while we are doing cleanup
  // They will be restored when Narcissus is reloaded.
  delete Narcissus.interpreter.global.setTimeout;
  delete Narcissus.interpreter.global.setInterval;

  Narcissus.interpreter.timeouts.forEach(function(timeoutId){
      clearTimeout(timeoutId);
  });
  Narcissus.interpreter.intervals.forEach(function(intervalId){
      clearInterval(intervalId);
  });
}

// Redirects to another site, for the purposes of example attack code.
Narcissus.interpreter.global.redirect = function(url) {
  var pc = Narcissus.interpreter.getPC();
  // Redirect is only permitted for trusted urls & computations.
  if (pc.isEmpty() && !(url instanceof Zaphod.facets.FacetedValue)) {
    content.document.location = url;
  }
  else Zaphod.log('Suppressed redirect attempt');
}

Narcissus.interpreter.global.addClickjacker = function(code) {
  //var f = function() {
  //  Narcissus.interpreter.evaluate(code);
  //}
  var f = code;
  content.document.addEventListener('click', f);
}

var originalJSON = JSON,
    originalJSONParse = originalJSON.parse;
Narcissus.interpreter.global.JSON.parse = function (json) {
  if (json instanceof Zaphod.facets.FacetedValue) {
    json = json.authorized;
  }
  return originalJSONParse.call(originalJSON, json);
};
Narcissus.interpreter.global.addPolicyFn = function(fn) {
  Zaphod.policy.addPolicyFn(fn);
}
