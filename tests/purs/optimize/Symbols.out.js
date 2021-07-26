"use strict";
var Data_Symbol = require("../Data.Symbol/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Proxy = require("../Type.Proxy/index.js");
var fooIsSymbol = {
    reflectSymbol: function () {
        return "foo";
    }
};
var set = function (dictIsSymbol) {
    var reflectSymbol = Data_Symbol.reflectSymbol(dictIsSymbol);
    return function (dictCons) {
        return function (l) {
            return function (a) {
                return function (r) {
                    return Record_Unsafe.unsafeSet(reflectSymbol(l))(a)(r);
                };
            };
        };
    };
};
var set1 = set(fooIsSymbol)();
var get = function (dictIsSymbol) {
    var reflectSymbol = Data_Symbol.reflectSymbol(dictIsSymbol);
    return function (dictCons) {
        return function (l) {
            return function (r) {
                return Record_Unsafe.unsafeGet(reflectSymbol(l))(r);
            };
        };
    };
};
var get1 = get(fooIsSymbol)();
var get2 = get({
    reflectSymbol: function () {
        return "bar";
    }
})();
var foo = Type_Proxy["Proxy"].value;
var h = function (n) {
    return set1(foo)(n)({
        foo: 0
    });
};
var f = function (n) {
    return get1(foo)({
        foo: n
    });
};
var bar = Type_Proxy["Proxy"].value;
var g = function (n) {
    return get2(bar)({
        foo: 0,
        bar: n
    });
};
module.exports = {
    get: get,
    set: set,
    foo: foo,
    bar: bar,
    f: f,
    g: g,
    h: h
};
