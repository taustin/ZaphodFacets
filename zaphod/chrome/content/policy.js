// We define a policy for which DOM elements should be tainted by wrapping certain functions.
// (Some) site-specific policies could be supported as well, provided care
// were taken to ensure that the policy code ran before any potential attack code.
// Of course, malicious chrome code might invalidate any of these policies.
// Piece at a time...
(function() {

// Passwords should be protected
 /*
var oldGetAttr = Element.prototype.getAttribute;
Element.prototype.getAttribute = function(attrName) {
  var attr = oldGetAttr.apply(this, arguments);
  if (oldGetAttr.call(this, 'type') === 'password') {
    return cloak(attr);
  }
  return attr;
}
*/

var oldGetById = document.getElementById;
document.getElementById = function() {
  var elem = oldGetById.apply(document, arguments);
  if (elem instanceof Element && elem.getAttribute('type')==='password') {
    elem.value = cloak(elem.value);
  }
  return elem;
}

})();
