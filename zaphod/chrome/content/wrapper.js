(function(policy) {
  //Helper for wrapping functions that return multiple elements
  function wrapElementsFn(oldGetter) {
    return function() {
      var elements = oldGetter.apply(this, arguments);
      policy.checkElements(elements);
      return elements;
    };
  }
  //Helper for wrapping functions that return a single element
  function wrapElementFn(oldGetter) {
    return function() {
      var element = oldGetter.apply(this, arguments);
      policy.checkElement(element);
      return element;
    };
  }

  document.getElementsByTagName = wrapElementsFn(document.getElementsByTagName);
  Element.prototype.getElementsByTagName = wrapElementsFn(Element.prototype.getElementsByTagName);

  document.getElementsByClassName = wrapElementsFn(document.getElementsByClassName);
  Element.prototype.getElementsByClassName = wrapElementsFn(
    Element.prototype.getElementsByClassName
  );

  document.getElementById = wrapElementFn(document.getElementById);

  var node_parentNodePD = Object.getOwnPropertyDescriptor(Node.prototype, 'parentNode');
  Object.defineProperty(Node.prototype, 'parentNode', {
    get: function() {
      var parentNode = node_parentNodePD.get.apply(this);
      if (parentNode && parentNode.nodeType === Node.ELEMENT_NODE) {
	policy.checkElement(parentNode);
      }
      return parentNode;
    }
  });
})(Zaphod.policy);
