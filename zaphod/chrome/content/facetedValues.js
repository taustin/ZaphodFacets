/* -*- Mode: JS; tab-width: 4; indent-tabs-mode: nil; -*-
 * vim: set sw=4 ts=4 et tw=78:
 * Faceted Value representation and corresponding details
 */
Zaphod = this.Zaphod || {};
Zaphod.facets = {};
(function(exports) {
    function FacetedValue(label, auth, unauth) {
        this.label = label;
        this.authorized = auth;
        this.unauthorized = unauth;
    }
    FacetedValue.prototype.toString = function() {
        //return '<' + this.label + '?' + this.authorized + ':' + this.unauthorized + '>';
        return uneval(this);
    }
    exports.FacetedValue = FacetedValue;

    function head(v) {
        if (v instanceof FacetedValue) {
            return v.label.unsigned();
        }
        if (v instanceof ProgramCounter && v.first()) {
            return v.first().unsigned();
        }
        else return MAX_LABEL;
    }

    exports.buildVal = function buildVal(pc, vn, vo) {
        var va = vn ? vn.authorized : vn,
            vb = vn ? vn.unauthorized : vn,
            vc = vo ? vo.authorized : vo,
            vd = vo ? vo.unauthorized : vo,
            rest = pc.rest();
        if (pc.isEmpty()) return vn;
        else if (head(pc) === head(vn) && head(vn) === head(vo)) {
            let k = vn.label;
            if (!pc.first().bar)
                return new FacetedValue(k, buildVal(rest,va,vc), vd);
            else
                return new FacetedValue(k, vc, buildVal(rest,vb,vd));
        }
        else if (head(vn) === head(vo) && head(vn) < head(pc)) {
            let k = vn.label;
            return new FacetedValue(k, buildVal(pc,va,vc), buildVal(pc,vb,vd));
        }
        else if (head(pc) === head(vn) && head(vn) < head(vo)) {
            let k = vn.label;
            if (!pc.first().bar)
                return new FacetedValue(k, buildVal(rest,va,vo), vo);
            else
                return new FacetedValue(k, vo, buildVal(rest,vb,vo));
        }
        else if (head(pc) === head(vo) && head(vo) < head(vn)) {
            let k = vo.label;
            if (!pc.first().bar)
                return new FacetedValue(k, buildVal(rest,vn,vc), vd);
            else
                return new FacetedValue(k, vc, buildVal(rest,vn,vd));
        }
        else if (head(pc) < head(vn) && head(pc) < head(vo)) {
            let firstLab = pc.first();
            let k = firstLab.bar ? firstLab.reverse() : firstLab;
            if (!firstLab.bar)
                return new FacetedValue(k, buildVal(rest,vn,vo), vo);
            else
                return new FacetedValue(k, vo, buildVal(rest,vn,vo));
        }
        else if (head(vn) < head(pc) && head(vn) < head(vo)) {
            let k = vn.label;
            return new FacetedValue(k, buildVal(pc,va,vo), buildVal(pc,vb,vo));
        }
        else if (head(vo) < head(pc) && head(vo) < head(vn)) {
            let k = vo.label;
            return new FacetedValue(k, buildVal(pc,vn,vc), buildVal(pc,vn,vd));
        }
        else {
            throw new Error('Unhandled case for buildVal');
        }
    }

    function Label(s, bar) {
        this.value = bar ? s.toUpperCase() : s.toLowerCase();
        this.bar = bar;
    }
    Label.prototype.reverse = function() {
        return new Label(this.value, !this.bar);
    }
    Label.prototype.unsigned = function() {
        return this.value.toLowerCase();
    }
    Label.prototype.toString = function() {
        return this.value;
    }
    exports.Label = Label;

    // FIXME: this is such a hack
    const MAX_LABEL= 'zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz';

    // Sorts alphabetically, but ignores case
    function compareLabels(a, b) {
        var al = a.unsigned();
            bl = b.unsigned();
        if (al === bl) return 0;
        else if (al === MAX_LABEL) return 1;
        else if (bl === MAX_LABEL) return -1;
        else if (al < bl) return -1;
        else return 1;
    }

    function ProgramCounter(initialLabel) {
        this.labelSet = [];
        if (initialLabel && !(initialLabel instanceof Label))
            throw new Error('Not a label');
        if (initialLabel) this.labelSet.push(initialLabel);
    }
    ProgramCounter.prototype.contains = function(label) {
        for (var i in this.labelSet) {
            let l = this.labelSet[i];
            if (l.value === label.value) return true;
        }
        return false;
    }
    // Only works for lower case strings
    ProgramCounter.prototype.containsStr = function(labelStr) {
        return this.contains(new Label(labelStr));
    }
    ProgramCounter.prototype.join = function(label) {
        if (this.contains(label)) return this;
        var newPC = new ProgramCounter();
        newPC.labelSet = this.labelSet.slice(0);
        newPC.labelSet.push(label);
        newPC.labelSet.sort(compareLabels);
        return newPC;
    }
    ProgramCounter.prototype.first = function() {
        if (this.labelSet.length < 1) return null;
        else return this.labelSet[0];
    }
    ProgramCounter.prototype.rest = function() {
        if (this.labelSet.length < 1) return EMPTY_PC;
        else {
            var newPC = new ProgramCounter();
            newPC.labelSet = this.labelSet.slice(1);
            return newPC;
        }
    }
    ProgramCounter.prototype.isEmpty = function() {
        return this.labelSet.length < 1;
    }
    ProgramCounter.prototype.toString = function() {
        return '{' + this.labelSet + '}';
    }

    exports.ProgramCounter = ProgramCounter;

    const EMPTY_PC = new ProgramCounter();

    exports.evaluateEach = function evaluateEach(v, f, x) {
        let pc = x.pc;
        if (!(v instanceof FacetedValue)) {
            return f(v, x);
        }

        if (pc.contains(v.label)) {
            return evaluateEach(v.authorized, f, x);
        }
        else if (pc.contains(v.label.reverse())) {
            return evaluateEach(v.unauthorized, f, x);
        }
        else {
            let va, vu;
            try {
                x.pc = pc.join(v.label);
                va = evaluateEach(v.authorized, f, x);
                x.pc = pc.join(v.label.reverse());
                vu = evaluateEach(v.unauthorized, f, x);
                x.pc = pc;
            }
            catch (e) {
                // Terminate program to avoid leaking data through exceptions
                //throw END_SIGNAL;
                throw e;
            }
            return new FacetedValue(v.label, va, vu);
        }
    }

    exports.evaluateEachPair = function evaluateEachPair(v1, v2, f, x) {
        let pc = x.pc;
        if (!(v1 instanceof FacetedValue || v2 instanceof FacetedValue)) {
            return f(v1, v2, x);
        }

        let k = head(v1) < head(v2) ? v1.label : v2.label;

        if (pc.contains(k)) {
            if (head(v1) === head(v2)) {
                return evaluateEachPair(v1.authorized, v2.authorized, f, x);
            }
            else if (v1 && v1.label === k) {
                return evaluateEachPair(v1.authorized, v2, f, x);
            }
            else {
                return evaluateEachPair(v1, v2.authorized, f, x);
            }
        }
        else if (pc.contains(k.reverse())) {
            if (head(v1) === head(v2)) {
                return evaluateEachPair(v1.unauthorized, v2.unauthorized, f, x);
            }
            else if (v1 && v1.label === k) {
                return evaluateEachPair(v1.unauthorized, v2, f, x);
            }
            else {
                return evaluateEachPair(v1, v2.unauthorized, f, x);
            }
        }
        else {
            if (head(v1) === head(v2)) {
                let va, vu;
                try {
                    x.pc = pc.join(k);
                    va = evaluateEachPair(v1.authorized, v2.authorized, f, x);
                    x.pc = pc.join(k.reverse());
                    vu = evaluateEachPair(v1.unauthorized, v2.unauthorized, f, x);
                    x.pc = pc;
                }
                catch (e) {
                    // Terminate program to avoid leaking data through exceptions
                    //throw END_SIGNAL;
                    throw e;
                }
                return new FacetedValue(k, va, vu);
            }
            else if (v1 && v1.label === k) {
                let va, vu;
                try {
                    x.pc = pc.join(k);
                    va = evaluateEachPair(v1.authorized, v2, f, x);
                    x.pc = pc.join(k.reverse());
                    vu = evaluateEachPair(v1.unauthorized, v2, f, x);
                    x.pc = pc;
                }
                catch (e) {
                    // Terminate program to avoid leaking data through exceptions
                    //throw END_SIGNAL;
                    throw e;
                }
                return new FacetedValue(k, va, vu);
            }
            else {
                let va, vu;
                try {
                    x.pc = pc.join(k);
                    va = evaluateEachPair(v1, v2.authorized, f, x);
                    x.pc = pc.join(k.reverse());
                    vu = evaluateEachPair(v1, v2.unauthorized, f, x);
                    x.pc = pc;
                }
                catch (e) {
                    // Terminate program to avoid leaking data through exceptions
                    //throw END_SIGNAL;
                    throw e;
                }
                return new FacetedValue(k, va, vu);
            }
        }
        throw new Error('Unhandlied case of evaluateEachPair');
    }

    exports.cloak = function(v, principal) {
        if (!principal)
            throw new Error('Must specify a principal.');
        let pc = Narcissus.interpreter.getPC();
        let lab = new Label(principal);
        if (pc.contains(lab))
            return v;
        else if (pc.contains(lab.reverse()))
            return undefined;
        else
            return new FacetedValue(new Label(principal), v, undefined);
    }

    // A view is represented as a program counter,
    // except that all labels can only be 'positive'.
    // If a label is not explicitly in the view,
    // the viewer sees the unauthorized view.
    exports.getView = function getView(v, view) {
        view = view || EMPTY_PC;
        if (v instanceof FacetedValue) {
            if (view.contains(v.label))
                return getView(v.authorized, view);
            else
                return getView(v.unauthorized, view);
        }
        else return v;
    }

    // Remove unneeded parts of a value.
    exports.strip = function strip(v, pc) {
        if (v instanceof FacetedValue) {
            if (pc.contains(v.label))
                return strip(v.authorized, pc);
            else if (pc.contains(v.label.reverse()))
                return strip(v.unauthorized, pc);
            else
                return new FacetedValue(v.label,
                    strip(v.authorized, pc),
                    strip(v.unauthorized, pc));
        }
        else return v;
    }

    // For some reason, chrome code sometimes loses track of the
    // type of the object, which I rely upon.
    // This rebuilds the value when needed.
    exports.rebuild = function rebuild(v) {
        if (!v) return v;
        if (v instanceof FacetedValue) return v;
        if (v.authorized === undefined) return v;
        let label = new Label(v.label.value);
        return new FacetedValue(label,
                rebuild(v.authorized),
                rebuild(v.unauthorized));
    }


})(Zaphod.facets);
