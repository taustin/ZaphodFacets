// Trusted code created by the website.
document.getElementById('slugform').addEventListener('submit', function(e) {
    e.preventDefault(); e.stopPropagation();
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


