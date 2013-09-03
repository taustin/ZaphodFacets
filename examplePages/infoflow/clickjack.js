// Redirect and addClickjacker are defined in Narcissus for convenience sake,
// though (with more work) updates to document.location could have been intercepted.
// To make the examples work without Narcissus, default implementations are given.
var redirect = this.redirect || function(url) {
  document.location = url;
}

var addClickjacker = this.addClickjacker || function(f) {
  document.addEventListener('click', f);
}


var newurl = "http://www.bias2build.com";
addClickjacker(function() { redirect(newurl); });

