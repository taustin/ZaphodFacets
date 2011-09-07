/* -*- Mode: JS; tab-width: 2; indent-tabs-mode: nil; -*-
 * vim: set sw=2 ts=2 et tw=100:
 *
 * This file holds utilities needed for dom.js.
 */

(function(exports) {

  // Copied from dom.js
  const MUTATE_VALUE = 1;
  const MUTATE_ATTR = 2;
  const MUTATE_REMOVE_ATTR = 3;
  const MUTATE_REMOVE = 4;
  const MUTATE_MOVE = 5;
  const MUTATE_INSERT = 6;
  const NUL = '\0';

  // Maps nid to host nodes
  var nodeMap={};

  const actions = [ 'abort', 'blur', 'change', 'click', 'dblclick', 'error',
        'focus', 'keydown', 'keypress', 'keyup', 'load', 'mousedown', 'mouseup',
        'mouseout', 'mouseover', 'mousemove', 'reset', 'resize', 'select', 'submit', 'unload' ];

  function addChild(parentNode, n, hostNode) {
    // Set a temporary mutation handler to build up the node map
    document.implementation.mozSetOutputMutationHandler(document, function(o){
        if (o.type === MUTATE_INSERT) {
          nodeMap[o.nid] = hostNode;
        }
        if (hostNode.addEventListener) {
          var oldAddEventListener = hostNode.addEventListener;
          hostNode.addEventListener = function(action, fun, capt) {
            var f = function() {
              return fun.apply(n, arguments);
            }
            return oldAddEventListener(action, f, capt);
          }
          n.addEventListener = function(a,f,c) {
            return hostNode.addEventListener(a,f,c);
          }
        }
    });
    parentNode.appendChild(n);
  }

  // Some cheats to deal with magic properties.  Not exhaustive
  function addMagicProperties(n, hostNode) {
    // Note -- this sidesteps the dom.js hooks, which complicates the analysis
    ['style', 'value', 'innerHTML', 'src', 'offsetLeft', 'offsetTop'].forEach(function(prop) {
      (function() {
        var val;
        Object.defineProperty(n, prop, {
          get: function() {
            if (isFacetedValue(val)) {
              return val;
            }
            val = hostNode[prop];
            return val;
            //return hostNode[prop];
          },
          set: function(newVal) {
            val = newVal;
            if (!isFacetedValue(newVal)) {
              // For ease of implementation, we ignore faceted writes.
              // Note that this differs from what happens in dom.js
              hostNode[prop] = newVal;
            }
          }
        });
        // Invalidate the value when the user enters a change.
        hostNode.addEventListener('change', function() { val=undefined; });
      })();
    });
  }

  // Clones hostNode as a dom.js node (using n as the clone, if it exists)
  // and adds the clone to the parentNode.
  function cloneNode(hostNode, parentNode, n) {
    var i, child;
    switch (hostNode.nodeType) {
      case Node.ELEMENT_NODE:
        if (!n) {
          n = document.createElement(hostNode.tagName);
          addMagicProperties(n, hostNode);
          addChild(parentNode, n, hostNode);
        }
        for (i=0; i<hostNode.childNodes.length; i++) {
          child = hostNode.childNodes[i];
          // A default title element is created by dom.js
          if (child.nodeName.toLowerCase() !== 'title') {
            cloneNode(child,n);
          }
        }
        for(i = 0; i < hostNode.attributes.length; i++) {
          var attr = hostNode.attributes[i];
          n.setAttribute(attr.name, attr.value);
        }
        break;
      case Node.PROCESSING_INSTRUCTION_NODE:
        n = document.createProcessingInstruction(hostNode.target, hostNode.data);
        addChild(parentNode, n, hostNode);
        break;
      case Node.TEXT_NODE:
        n = document.createTextNode(hostNode.data);
        addChild(parentNode, n, hostNode);
        break;
      case Node.COMMENT_NODE:
        n = document.createComment(hostNode.data);
        addChild(parentNode, n, hostNode);
        break;
      default:
        Zaphod.log('unhandled node type: ' + hostNode.nodeType);
    }
  }

  // Create a spidermonkey node from a dom.js node
  function createHostNode(domjsNodeStr, nid) {
    var n, substrArr, s, t, i, parentNode;

    // Check to see if the host node already exists
    if (nodeMap[nid]) return nodeMap[nid];

    substArr = domjsNodeStr.split(NUL);
    for (i=0; i<substArr.length; i++) {
      t = substArr[i].charAt(0);
      s = substArr[i].slice(1);
      if (t === '') break;
      switch (t) {
        case 'T':
          n = hostDoc.createTextNode(s)
          break;
        case 'C':
          n = hostDoc.createComment(s);
          break;
        case 'H':
        case 'E':
          n = hostDoc.createElement(s);
          if (parentNode) parentNode.appendChild(n);
          parentNode = n;
          break;
        default:
          throw new Error('Unhandled case of stringified node: ' + t);
      }
      if (!nodeMap[nid]) nodeMap[nid] = n;
    }

    return n;
  }

  function insertAtPosition(parentId, hostNode, position) {
    var parentNode = nodeMap[parentId],
        beforeNode = parentNode.childNodes[position];
    parentNode.insertBefore(hostNode, beforeNode);
  }

  // The auth function should take a faceted value and returns true
  // if the high view is authorized, and false otherwise.
  // If auth is undefined, the authorized view will be rendered to the host DOM.
  function parseFacetedValue(fv, auth) {
    if (!fv) return fv;
    if (!auth || auth(fv))
      return getAuth(fv);
    else
      return getUnAuth(fv);
  }

  // Hard-coded nids
  const DOCUMENT_NID = 1,
        BODY_NID = 7;
  exports.copyDOMintoDomjs = function() {
    // FIXME: need a better way to map the document
    nodeMap[DOCUMENT_NID] = hostDoc;

    var head = document.getElementsByTagName('head')[0];
    var hostHead = hostDoc.getElementsByTagName('head')[0];
    cloneNode(hostHead, document, head);

    var title = document.getElementsByTagName('title')[0];
    var hostTitle = hostDoc.getElementsByTagName('title')[0];
    if (hostTitle) title.firstChild.nodeValue = hostTitle.firstChild.data;

    var body = document.getElementsByTagName('body')[0];
    var hostBody = hostDoc.getElementsByTagName('body')[0];
    body.style = hostBody.style;
    cloneNode(hostBody, document, body);
    // FIXME: need a better way to map the body
    nodeMap[BODY_NID] = body;

    // Cheat: creating getter/setter pair for scrollTop
    Object.defineProperty(body, 'scrollTop', {
        get: function() { return hostBody.scrollTop; }
    });

    document.body = body;

    // Callback handler registers mutation events to reflect changes in the host DOM.
    document.implementation.mozSetOutputMutationHandler(document, function(o){
      var hostNode, parentNode, newVal, auth;
      var s = '';
      for (var i in o) {
        s += i + ':' + o[i] + ' ';
      }
      //alert('mutations... ' + s);
      switch(o.type) {
        case MUTATE_VALUE:
          nodeMap[o.target].data = o.data;
          break;
        case MUTATE_ATTR:
          // Src attributes might load data from external sites.
          // Use the public view if that happens.
          // (Note: this policy is for a demo, and is not intended
          // to be anything approaching comprehensive at this point).
          auth = function(fv) {
            if (o.name !== 'src') return true;
            var authorized = getAuth(fv);
            return authorized.indexOf('http') !== 0;
          }
          newVal = parseFacetedValue(o.value, auth);
          if (o.ns === null && o.prefix === null) {
            nodeMap[o.target].setAttribute(o.name, newVal);
          }
          else {
            // TODO: need to test this version
            nodeMap[o.target].setAttributeNS(o.ns, o.name, newVal);
          }
          break;
        case MUTATE_REMOVE_ATTR:
          nodeMap[o.target].removeAttribute(o.name);
          break;
        case MUTATE_REMOVE:
          hostNode = nodeMap[o.target];
          hostNode.parentNode.removeChild(hostNode);
          break;
        case MUTATE_MOVE:
          hostNode = nodeMap[o.target];
          insertAtPosition(o.parent, hostNode, o.index);
          break;
        case MUTATE_INSERT:
          hostNode = createHostNode(o.child, o.nid);
          insertAtPosition(o.parent, hostNode, o.index);
          break;
        default:
          throw new Error('Unhandled mutation case: ' + MUTATE_VALUE);
      }
    });
  }

  // Set listeners to use Narcissus
  exports.handleListeners = function() {
    Zaphod.log('Loading listeners for dom.js');
    var elems = hostDoc.getElementsByTagName('*');
    for (var i=0; i<elems.length; i++) {
      var elem = elems[i];
      for (var j=0; j<actions.length; j++) {
        var action = actions[j];
        if (elem.getAttribute('on' + action)) {
          (function() {
            var el = elem;
            var code = el.getAttribute('on' + action);
            var eventName = code.replace(/.*?\((.*?)\).*/, "$1");
            var fun = function(evnt) {
              this[eventName] = evnt;
              with (el) {
                eval(code);
              }
            };
            el.addEventListener(action,
                fun,
                false);
            // Fire load actions immediately
            if (action === "load") {
              fun();
            }
          })();
        }
      }
    }
  }

})(this);

