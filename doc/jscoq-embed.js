/**
 * Injects jsCoq into an existing page.
 * This script has to be at the end of the body so that it runs after
 * the page DOM has loaded.
 */

var RealWorker = window.Worker;

var Worker = function(url) {
    var blob = new Blob([`importScripts('${url}');`],
        { "type": 'application/javascript' });
    return new RealWorker(URL.createObjectURL(blob));
}

function jsCoqInject() {
    document.body.classList.add('hands-off', 'toggled');
    document.body.id = 'ide-wrapper';
}

var jsCoqShow = (localStorage.jsCoqShow !== 'false');

var jscoq_ids  = ['#main > div.code'];
var jscoq_opts = {
    show:      jsCoqShow,
    focus:     false,
    replace:   true,
    pkg_path:  'https://jscoq.github.io/node_modules/jscoq/coq-pkgs/',
    editor:    { mode: { 'company-coq': true }, keyMap: 'default' },
    all_pkgs:  ['init',
                'coq-base', 'coq-collections', 'coq-arith', 'coq-reals'],
    init_pkgs: ['init'],
    init_import: ['utf8'],
    implicit_libs: true
};

function jsCoqLoad() {
    // - remove empty code fragments (coqdoc generates some spurious ones)
    for (let sel of jscoq_ids) {
        for (let el of document.querySelectorAll(sel)) {
            if (el.textContent.match(/^\s*$/)) {
                el.parentElement.insertBefore(document.createElement('p'), el);
                el.remove();
            }
        }
    }

    JsCoq.start(/*jscoq_opts.base_path, '../../node_modules/', */jscoq_ids, jscoq_opts)
        .then(coq => {
            window.coq = coq;
            window.addEventListener('beforeunload', () => { localStorage.jsCoqShow = coq.layout.isVisible(); });
            document.querySelector('#page').focus();
        });
    
    if (jscoq_opts.show)
        document.body.classList.add('jscoq-launched');
}

function jsCoqStart() {
    document.body.classList.remove('jscoq-launched');
    coq.layout.show();
}

if (location.search === '') {
    jsCoqInject();
    jsCoqLoad();
}
