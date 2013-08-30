// We define a policy for which DOM elements should be tainted by wrapping certain functions.
// (Some) site-specific policies could be supported as well, provided care
// were taken to ensure that the policy code ran before any potential attack code.
// Of course, malicious chrome code might invalidate any of these policies.
// Piece at a time...
var oldGetById = document.getElementById;
document.getElementById = function() {
  var elem = oldGetById.apply(document, arguments);
  if (elem instanceof Element && elem.getAttribute('type')==='password') {
    elem.value = cloak(elem.value);
  }
  return elem;
}

Zaphod = this.Zaphod || {};
var policyFns = [];
Zaphod.policy = {
  checkElement: function(element) {
    policyFns.forEach(function(policyFn) {
      policyFn(element);
    });
  },
  //Only call this with NodeList. That's all it's being called with right now, so I'm not going to
  //bother covering Arrays just yet.
  checkElements: function(elements) {
    if (elements instanceof NodeList) {
      for (var i = 0; i < elements.length; i++) {
	Zaphod.policy.checkElement(elements.item(i));
      }
    }
  },
  addPolicyFn: function(policyFn) {
    policyFns.push(policyFn);
  }
};
