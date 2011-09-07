// Trusted code created by the website.
var b = document.getElementById('passBut');
b.addEventListener('click', function() {
    var p = document.getElementById('pass');
    var pwd = p.value || 'default';
    var hash = hex_md5(pwd);
    // Simulate server-side check here.
    if (hash === PWD_HASH) {
      alert('Authentication successful');
    }
    else {
      alert('Please try again');
    }
});


