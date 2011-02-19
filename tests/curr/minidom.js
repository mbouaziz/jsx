/*

Partial and simplified model of the DOM
Inspired by env-js by John Resig

*/

var option_selectedIndex = false;
/* option_selectedIndex

  if true, will force branching on SelectElement.change()

  if false, OptionElement won't have a .selected
  and SelectElement won't have a .selectedIndex
  and SelectElement.value will be a symbolic value
 */


var XMLHttpRequest = function() {
    this.open = function(method, uri, async) {
	output("XMLHttpRequest.uri", uri);
	this.responseText = null;
	this.status = 0;
    };
    this.send = function(body) {
	this.responseText = symbol_string("responseText");
	this.status = symbol_int("status");
    };
};

var HTMLDocument,
    HTMLElement,
    HTMLFormElement,
    HTMLInputElement,
    HTMLLabelElement,
    HTMLOptionElement,
    HTMLSelectElement;

var Element, Node, Text;

var Event = function(name, handler) {
    this.name = name;
    this.handler = handler;
};
Event.prototype.trigger = function(node) {
    output("events", node.id + "." + this.name);
    if (this.handler)
	this.handler.apply(node);
    var user = node.getAttribute("on" + this.name)||"";
    if (user !== "")
	eval(user);
};

var Events = new (function() {

  var nbId = 0;
  var nodes = {};
  var nbNodes = 0;
  this.newId = function() { return nbId++; };
  this.register = function(obj, events) {
      var eventsId = obj.eventsId;
      if (events.length == 0) {
	  if (nodes[eventsId] !== undefined) {
	      nodes[eventsId] = undefined;
	      nbNodes--;
	  }
      } else {
	  if (nodes[eventsId] === undefined)
	      nbNodes++;
	  nodes[eventsId] = {obj:obj, events:events};
      }
  };
  var rand_generateEventForNode = function (obj_events) {
      var length = obj_events.events.length;
      var obj = obj_events.obj;
      if (length == 1)
	  obj_events.events[0].trigger(obj);
      else {
	  var numEv = symbol_int("evE_" + obj.id);
	  assume(numEv >= 0);
	  assume(numEv < length);
	  for (var i = 0 ; i < length ; i++)
	      if (i === numEv)
		  return obj_events.events[i].trigger(obj);
      }
  };
  this.rand_generate = function (n) {
      if (n <= 0) return undefined;
      var numNode = symbol_int("evN");
      assume(numNode >= 0);
      assume(numNode < nbNodes);
      var curNum = 0;
      for (var nodeEventsId in nodes) { // trick to have a concrete get-field
	  if (nodes[nodeEventsId] === undefined)
	      continue;
	  if (numNode === curNum) {
	      rand_generateEventForNode(nodes[nodeEventsId]);
	      break;
	  }
	  curNum++;
      };
      this.rand_generate(n-1);
  };
    
}) ();

Node = function() {
    this.nodeName = "";
    this.nodeValue = null;
    this.childNodes = new Array();
    this.attributes = null;
    this.eventsId = Events.newId();
};
Node.prototype.appendChild = function(newChild) {
    if (!newChild)
	return null;
    this.childNodes.push(newChild);
    return newChild;
};
Node.prototype.__registerEvents__ = function() { Events.register(this, arguments) };

// merge of Text & CharacterData
Text = function() { Node.apply(this, arguments); };
Text.prototype = new Node();
Object.defineProperty(Text.prototype, "data",
   { get: function() { return this.nodeValue; },
     set: function(data) { this.nodeValue = data; }
   });

Element = function() {
    Node.apply(this, arguments);
    this.attributes = new Array();
};
Element.prototype = new Node();
Element.prototype.getAttribute = function(name) { return this.attributes[name]; };
Element.prototype.setAttribute = function(name, value) { this.attributes[name] = value+''; };
Object.defineProperty(Element.prototype, "tagName", { get: function() { return this.nodeName; }});

HTMLElement = function() { Element.apply(this, arguments); };
HTMLElement.prototype = new Element();
Object.defineProperty(HTMLElement.prototype,"id",
   { get: function() { return this.getAttribute("id"); },
     set: function(id) { this.setAttribute("id", id); }
   });
HTMLElement.prototype.setAttribute = function(name, value) {
    var res = Element.prototype.setAttribute.apply(this, arguments);
    var callback = HTMLElement.getAttributeCallback('set', this.tagName, name);
    if (callback)
	callback(this, value);
};
HTMLElement.attributeCallbacks = {};
HTMLElement.registerSetAttribute = function(tag, attrib, callbackfn) {
    HTMLElement.attributeCallbacks[tag + ':set:' + attrib] = callbackfn;
};
HTMLElement.getAttributeCallback = function(type, tag, attrib) {
    return HTMLElement.attributeCallbacks[tag + ':' + type + ':' + attrib] || null;
};

HTMLBodyElement = function() { return HTMLElement.apply(this, arguments); };
HTMLBodyElement.prototype = new HTMLElement();

var HTMLInputCommon = function() { HTMLElement.apply(this, arguments); this.__updateEvents__(); };
HTMLInputCommon.prototype = new HTMLElement();
HTMLInputCommon.prototype.__updateEvents__ = function() {};
HTMLInputCommon.prototype.setAttribute = function(name, value) {
    var res = HTMLElement.prototype.setAttribute.apply(this, arguments);
    if (name === "type" || name === "disabled")
	this.__updateEvents__();
    return res;
};
Object.defineProperty(HTMLInputCommon.prototype,"disabled",
   { get: function() { return (this.getAttribute("disabled") === "disabled"); },
     set: function(value) { this.setAttribute("disabled", (value ? "disabled" : "")); }
   });

var HTMLTypeValueInputs = function(){ HTMLInputCommon.apply(this, arguments); };
HTMLTypeValueInputs.prototype = new HTMLInputCommon();
Object.defineProperty(HTMLTypeValueInputs.prototype,"name",
   { get: function() { return this.getAttribute("name")||""; },
     set: function(value) { this.setAttribute("name", value); }
   });
var HTMLInputAreaCommon = function(){ HTMLTypeValueInputs.apply(this, arguments); };
HTMLInputAreaCommon.prototype = new HTMLTypeValueInputs();

HTMLFormElement = function(){ HTMLElement.apply(this, arguments); };
HTMLFormElement.prototype = new HTMLElement();

HTMLInputElement = function(){ HTMLInputAreaCommon.apply(this, arguments); };
HTMLInputElement.prototype = new HTMLInputAreaCommon();
Object.defineProperty(HTMLInputElement.prototype,"value",
  { get: function() { return this._value; },
    set: function(newvalue) {
            output(this.id + ".value", newvalue);
            this._value = newvalue;
         }
  });
var __input_text_change__ = new Event("change", function () { this._value = symbol_string(this.id + ".value"); } );
var __button_click__ = new Event("click", null);
HTMLInputElement.prototype.__updateEvents__ = function () {
    if (this.disabled)
	return this.__registerEvents__();
    switch (this.type) {
    case "button": return this.__registerEvents__( __button_click__);
    case "text": return this.__registerEvents__( __input_text_change__);
    }
};
HTMLInputElement.prototype.click = function() { if (this.type === "button") __button_click__.trigger(this); };
HTMLInputElement.prototype.change = function() { if (this.type === "text") __input_text_change__.trigger(this); };
Object.defineProperty(HTMLInputElement.prototype,"type",
  { get: function() { return this.getAttribute("type") || "text"; },
    set: function(value) { this.setAttribute("type", value); }
  });

HTMLElement.registerSetAttribute('input', 'value', function(node, value) {
  node._value = value;
  output(node.id + ".value", value);
});

HTMLLabelElement = function() { HTMLInputCommon.apply(this, arguments); };
HTMLLabelElement.prototype = new HTMLInputCommon();

HTMLOptionElement = function() {
    HTMLInputCommon.apply(this, arguments);
    this._selected = null;
};
HTMLOptionElement.prototype = new HTMLInputCommon();
if (option_selectedIndex) {
    Object.defineProperty(HTMLOptionElement.prototype,"selected", {
      get: function() { return this._selected; },
      set: function(value) { this._selected = value?true:false; }
	});
}

HTMLSelectElement = function() { HTMLTypeValueInputs.apply(this, arguments); };
HTMLSelectElement.prototype = new HTMLTypeValueInputs();
if (option_selectedIndex) {
    var __select_value__ = {
	get: function() {
	    var index = this.selectedIndex;
	    return (index === -1) ? '' : this.options[index].value;
	}};
    var __select_change__ = new Event("change", function () {
	    var selIdx = symbol_int(this.id + ".selectedIndex");
	    assume(selIdx >= 0);
	    assume(selIdx < this.options.length);
	    this.selectedIndex = selIdx;
	});
} else {
    var __select_value__ = { get: function() { return this._value; } };
    var __select_change__ = new Event("change", function () { this._value = symbol_string(this.id + ".value"); });
}
Object.defineProperty(HTMLSelectElement.prototype,"value", __select_value__);
HTMLSelectElement.prototype.__updateEvents__ = function() {
    if (this.disabled)
	return this.__registerEvents__();
    this.__registerEvents__( __select_change__);
};
HTMLSelectElement.prototype.change = function() { __select_change__.trigger(this); };
Object.defineProperty(HTMLSelectElement.prototype,"options", { get: function() { return this.childNodes; } });
if (option_selectedIndex) {
  Object.defineProperty(HTMLSelectElement.prototype,"selectedIndex",
    { get: function() {
	    var options = this.options;
	    var imax = options.length;
	    for (var i=0; i < imax; ++i)
		if (options[i].selected)
		    return i;
	    return -1;
	},
     set: function(value) {
	    var options = this.options;
	    var num = +value;
	    var imax = options.length;
	    for (var i=0; i < imax; ++i)
		options[i].selected = (i == num);
	}
    });
}

// Merge HTMLDocument & Document
HTMLDocument = function() { Node.apply(this, arguments); };
HTMLDocument.prototype = new Node();
HTMLDocument.prototype.createElement = function(tagName) {
    var node;
    switch(tagName){ // should be toUpperCase
    case "body": node = new HTMLBodyElement(this); break;
    case "form": node = new HTMLFormElement(this); break;
    case "input": node = new HTMLInputElement(this); break;
    case "label": node = new HTMLLabelElement(this); break;
    case "option": node = new HTMLOptionElement(this); break;
    case "select": node = new HTMLSelectElement(this); break;
    };
    node.nodeName = tagName;
    return node;
};
HTMLDocument.prototype.createTextNode = function(data) {
    var node = new Text(this);
    node.data = data;
    return node;
};    
HTMLDocument.prototype.getElementById = function(elementId) {
    var rec = function (node) {
	if (node.id == elementId)
	    return node;
	var childNodes = node.childNodes;
	for (var i=0;i<childNodes.length;i++)
	    {
		var ret = rec(childNodes[i]);
		if (ret != null)
		    return ret;
	    }
	return null;
    };
    return rec(this);
};
Object.defineProperty(HTMLDocument.prototype, "documentElement", { get : function() { return this.childNodes[0]; }});

var document = (function(){
  var document = new HTMLDocument();
  document.appendChild(document.createElement("body"));
  return document;
}());

var alert = function(s) { output("alert", s); };
