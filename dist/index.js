function _interopDefault (ex) { return (ex && (typeof ex === 'object') && 'default' in ex) ? ex['default'] : ex; }

var React = _interopDefault(require('react'));
var ReactTooltip = _interopDefault(require('react-tooltip'));

function _extends() {
  _extends = Object.assign || function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];

      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }

    return target;
  };

  return _extends.apply(this, arguments);
}

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

var reactIs_production_min = {
	AsyncMode: AsyncMode,
	ConcurrentMode: ConcurrentMode,
	ContextConsumer: ContextConsumer,
	ContextProvider: ContextProvider,
	Element: Element,
	ForwardRef: ForwardRef,
	Fragment: Fragment,
	Lazy: Lazy,
	Memo: Memo,
	Portal: Portal,
	Profiler: Profiler,
	StrictMode: StrictMode,
	Suspense: Suspense,
	isAsyncMode: isAsyncMode,
	isConcurrentMode: isConcurrentMode,
	isContextConsumer: isContextConsumer,
	isContextProvider: isContextProvider,
	isElement: isElement,
	isForwardRef: isForwardRef,
	isFragment: isFragment,
	isLazy: isLazy,
	isMemo: isMemo,
	isPortal: isPortal,
	isProfiler: isProfiler,
	isStrictMode: isStrictMode,
	isSuspense: isSuspense,
	isValidElementType: isValidElementType,
	typeOf: typeOf
};

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;
var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
// (unstable) APIs that have been removed. Can we remove the symbols?

var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
}

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;

    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;

          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;

              default:
                return $$typeof;
            }

        }

      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
} // AsyncMode is deprecated along with isAsyncMode

var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;
var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }

  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
exports.isValidElementType = isValidElementType;
exports.typeOf = typeOf;
  })();
}
});

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret;

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning$1(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning$1(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has$1(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning$1(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
          return null;
        }
      }

      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from
      // props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

var iransStatesProperties = [{
  id: "b1",
  parentId: "a1",
  name: "alborz",
  persianName: "البرز",
  persianNickName: "البرز",
  ltrRotate: -30,
  ltrX: 220,
  ltrY: 475,
  d: "M404.6,321.3c-0.8-0.7-3.6-2.9-5.2-3.8c-1-0.5-1.6-1.5-1.6-2.7c0-1.2,0.6-2.2,1.6-2.7c1.9-0.9,2.9-6.3,2.9-8.3c0-1.4,1.7-2.8,4.1-4.6c1-0.7,1.8-1.4,2.5-2.1c0.6-0.6,1.4-1.7,2.3-2.9c2.4-3.3,5.4-7.4,8.4-8.2c3.6-0.9,6-2.6,6.4-2.9l0,0c0.3-0.5,1-1.8,0.7-2.9c-0.2-0.7-0.7-1.2-1.6-1.6l-0.5-0.2c-7.6-3.3-9.3-4.5-9.6-5.4c-0.1-0.2-0.2-0.6-0.4-1c-0.9-1.9-1.8-4.1-0.9-5.5c0.4-0.8,1.3-1.2,2.5-1.3c2.5-0.2,4.9-0.4,6.9-0.4c1.4,0,3.4,0.1,4.7,0.4c1.4,0.4,5.6,0.7,8.8,1l0.2,0l0.2,0.1c1.7,0.8,10.1,5.1,12.4,7c2.3,1.8,9.9,3.7,12.4,4.3l0.5,0.1c2,0.5,8.1,1,10.4,1c0.7,0,1.6,0.1,2.5,0.4l0.8,0.2l-0.1,0.8c-0.2,1.7-0.6,4.9-0.9,6.4c-0.2,0.8-0.6,1.4-1,2.1c-0.6,1-1.4,2.2-2,4.9c-0.5,2.2-1.9,3.3-4.2,3.3l0,0c-1,0-2.1-0.2-3.5-0.4c-0.4-0.1-0.8-0.1-1.1-0.2c-0.2,0-0.5-0.1-0.7-0.1c-1.9,0-3.5,1.4-5.1,2.8c-0.5,0.4-1,0.8-1.4,1.2c-1.4,1.1-2,2.5-2.6,4c-0.5,1.2-1,2.3-1.9,3.4c-2.4,2.9-6,3.1-6.7,3.1c-0.5,0-1.6,0.1-2.7,0.1c-2.8,0.2-6.9,0.4-11.3,0.4c-5.3,0-10.4,0.7-14.2,1.2c-0.9,0.1-1.6,0.2-2.3,0.3c-3.5,0.4-4.2,6.2-4.3,7.1l1.8,1.6l-2.5,0.1c-1.6,0.1-3,0.1-3.7,0.2l-0.4,0L404.6,321.3z"
}, {
  id: "b2",
  parentId: "a1",
  name: "ardebil",
  persianName: "اردبیل",
  persianNickName: "اردبیل",
  ltrRotate: 50,
  ltrX: 250,
  ltrY: -130,
  d: "M306.3,208.4c-0.5,0-0.9-0.2-1.5-0.4c-0.3-0.1-0.6-0.2-0.9-0.3c-1.5-0.4-2.2-1.9-2.2-2.7c0-0.5-0.4-1.3-0.9-1.9l-3-0.8l-0.2-0.4c-0.3-0.6-0.6-1.2-0.8-1.5c0,0-0.3-0.3-1.8-0.3c-0.4,0-0.9,0-1.3,0.1l-0.3,0l-3.3-2.1l-2.7-3.7l-2.6-1.3l-3.1-3.1l-0.1-0.3c-0.2-0.6-1-3.7-1-5.2c0-1.1-1-3.5-2-5.2c-0.5-0.8-2.2-3.5-3.3-4.6c-0.3-0.3-0.7-1-0.6-1.9c0.2-1.2,1.3-2.5,2.6-3.2c1.7-0.8,3.3-1.4,3.9-1.6c0.3-2.4,0.6-5.2,0.6-6.1c0-1.2-1.9-2.8-3.5-3.4l-0.5-0.2c-1.6-0.6-3.8-1.5-6.5-2.1c-0.9-0.2-1.5-0.5-1.7-1l-0.1-0.1l0-0.1c-0.2-0.7,0.4-1.6,2.1-2.9c0.2-0.1,0.3-0.3,0.3-0.5c0-0.6-1-1.4-2-2.4c-1-0.9-2.2-1.9-3-3.2c-1.4-2.1-1.4-3.9-1.3-5.8c0-0.8,0-1.7-0.1-2.6c-0.3-2.4-0.8-6.3-1-7.7c-1.6,0.4-4.4,1.3-5.6,2.5c-0.7,0.7-2,1-4.3,1c-1.2,0-2.5-0.1-3.5-0.2c-0.9-0.1-1.8-0.1-2.4-0.1c-1.7,0-6-0.3-9.2-3.1c-2-1.7-6.7-3.9-8.6-4.7l-1.7-0.8l1.6-1c1.7-1,4.6-2.9,5.8-3.6c1.7-1,4.6-4.7,4.9-5.5c0.3-1,3-7,3.7-8.1c0.2-0.3,0.6-0.6,1.1-1.2c0.7-0.6,1.6-1.5,1.5-1.9c0-0.1-0.1-0.1-0.2-0.2c-0.9-0.5-3.4-1.9-5.4-3l-0.8-0.5l2.9-5.7l0.7,0.1c0.4,0,1.1,0.1,1.9,0.3c0.2,0,0.4,0.1,0.7,0.1c1.3,0,2.8-0.6,3-1.2c0.5-1.5,0.6-2.9-1.5-4c-2.1-1-1.6-5-1-9c0.1-0.8,0.2-1.5,0.2-1.9c0-0.8-0.4-4.4-0.8-8.3l0-0.2c-0.5-5-0.9-8.9-0.9-9.9c0-2-0.3-3.5-1.9-4.8c-1.1-0.9-5-3.2-8.3-5.1l-1.3-0.7l2.4-1.9l2.6-1.3l4.3-1.4l1.2-0.1l0.5-0.3l3.1-2.9l8.1-4.1l3.4-3.2l1.3-0.8l1.7-0.5l4.5,0.1l0.4-0.1l0.4-0.3l1-1.3l1.6,0.4l1.4,0.8l3.6,3.2l9.9,10.7l4,3.4l1.7,2.3l1.9,3.7l-3.1,0.9l-3.1,1.9l-3.8,0.7l-1.7,0.8l-1.5,1.3l-0.9,1.6l-0.1,1.8l0.7,1.6l1.3,1.6l3.1,2.8l3.4,1.3l1.2,1.1l1.8,3.7l0.4,1.1v1.3l-0.4,1.2l-0.5,1l-0.8,1l-2.7,1.6L277,85.5v0.2l-0.2,0.9l-3.3,1.9l-0.2,0.3l0.1,2.3l0.9,1.6l3.6,2.6l7.7,3.5l1,0.9l0.7,2.1l-0.3,1.4l0,0.6l2.7,1.9l0.9,1.3l0.7,0.6h1.2l2.9-1.3h2.3l1,2.2l0.4,1.8l0.5,0.6l1,0.8l0.9,1.4l1,1l0.9,1.1l2.2,2.6l1.6,2.4l1.5,1.4l2.9,0.2l-1,1.4l2.5,9.9l0,0.2c-0.5,3.7-1,8.4-1,9.8c0,1.8-0.9,6-4.1,8.7c-2.4,2-1.1,4.9,0.6,8.3c0.2,0.3,0.3,0.6,0.4,0.9c1.5,3,2.6,5.6,1,8.7c-1.4,2.8-1,5.7,0.9,7.2c1.9,1.5,4.8,6.6,6.1,9.1c0.7,1.3,1.8,2.7,2.9,4c0.6,0.7,1.1,1.4,1.6,2c1.6,2.1,1.6,5.1,1.6,8.6c0,1.2,0.4,2.4,1.1,3.4l0.6,0.9l-1,0.5c-1,0.6-3,1-4.5,1c-0.7,0-1.3-0.1-1.6-0.4c-0.7-0.4-2.1-0.5-3.4-0.6c-1-0.1-2-0.1-2.6-0.4c-0.1,0-0.2-0.1-0.4-0.1c-0.6,0-1.8,0.4-3.9,2.5C307.3,208.2,306.8,208.4,306.3,208.4z"
}, {
  id: "b3",
  parentId: "a1",
  name: "azerbaijansharghi",
  persianName: "آذربایجان شرقی",
  persianNickName: "آذربایجان شرقی",
  ltrRotate: 0,
  ltrX: 135,
  ltrY: 150,
  d: "M212,235.1c-1-0.6-3.6-2-4.9-3.1c-0.6-0.5-1.2-1.4-0.7-3.1c0.3-1,0.9-2.2,1.7-3.2c0.7-0.9,0.6-1.3-1.2-3.1c-0.5-0.5-1.1-1.1-1.8-1.9c-2-2.3-1.6-4.9-0.9-6.3l-8.2-1.9c-0.5,0.4-2.6,2.1-5,3.3c-0.9,0.5-2.3,0.7-4.1,0.7c-2.8,0-5.9-0.5-7.8-1c-0.2,0-0.3-0.1-0.5-0.1c-1.8,0-3.8,2.6-5.2,4.5c-0.4,0.6-0.8,1.1-1.1,1.4c-0.8,1-2,1.4-3.5,1.4c0,0,0,0,0,0c-1.6,0-3.7-0.6-6.2-1.7c-3.9-1.8-3.7-4.2-3.5-5.4c0-0.2,0-0.3,0-0.5c0-1.2-0.5-4.4-0.7-5.3c-0.3-1.9-4.6-3.8-5.8-3.8c-0.6,0-1.7-0.2-3.4-0.7c-1.6-0.4-3.4-0.8-5-1c-3-0.3-7.9-6.4-8.5-7l-10.1-15.1L108.7,137l-3.7-6.7l0-0.1c-0.1-0.1-1.3-3.7-1.3-5v-5.8l0.6-0.3c0.5-0.2,4.8-1.9,7.5-3.1c1.9-0.8,2.7-1.5,3.4-2.2c0.5-0.4,0.9-0.8,1.5-1.1c0.3-0.2,0.4-0.4,0.5-0.8c0.4-1.6-1.1-4.3-1.9-5.5c-1.4-2.1-1.4-5.5-1.4-7.2c0-1.6,0-6.3,0.3-8.7l0-0.2c0.3-2.3,0.7-5,2.7-6.6c1.8-1.5,4.2-3.6,4.6-3.9c0,0,0.8-0.9,0.8-0.9l1.1,1.2l1.1,0.6l1.1,0.5l1.6,0.4l1.3,0.7l0.5,0.1l1.6,0.1l3.3,0.7l5.3,0.1l4.5,1.6l12.3,2.3l3.9,1.7l3.2,0.7h0.4l3.7-0.5l0.8-0.4l3-2l1.3-0.6l0.9-0.3h2.3l1.4-0.5h0.9l1,0.1l6.2,2.6l0.7,0.2l0.8-0.1l1-0.3l0.9-0.5l0.8-0.6l0.7-0.7l0.6-0.9l1.6-3.1l0.9-1.2l1.3-0.9l3.4-1.6l0.6-0.6l0.9-2l0.8-1.2L201,74l1-0.5l0.3-0.2l0.2-0.2l1.5-2.4l0.9-1l1.1-0.8l1.3-0.5h1.3l1.7,0.7l0.6,0.1l0.4-0.1l3.3-1.8l0.2-0.1l0.5-0.5l0.2-0.3l0.9-2.7l2.2-3.1l0.2-0.6l0.7-0.9l3-1.7l5.9-2.1l2.2-1.2l1.8-1.7l3.1-3.6l0.8,0.6c1,0.6,7.1,4.1,8.6,5.3c1.7,1.4,2.1,3.1,2.1,5.2c0,1,0.5,5.7,0.9,9.8l0,0.2c0.5,4.6,0.8,7.6,0.8,8.3c0,0.4-0.1,1-0.2,2c-0.4,2.6-1.1,7.5,0.8,8.5c2.9,1.4,2.1,3.7,1.8,4.6c-0.4,1.1-2.4,1.6-3.4,1.6c-0.3,0-0.6,0-0.9-0.1c-1-0.2-1.8-0.3-2.1-0.3l-2.5,5c1.1,0.6,4.4,2.5,5.7,3.1l0.9,0.5l-0.5,0.9c-0.3,0.5-0.9,1-1.5,1.6c-0.4,0.4-0.8,0.8-1,1.1c-0.6,1-3.3,6.9-3.6,7.9c-0.4,1.1-3.4,4.8-5.1,5.8c-1.3,0.8-5,3.1-6.6,4.1c1.6,0.7,7.3,3.2,9.6,5.2c3,2.7,7.2,2.9,8.8,2.9c0.7,0,1.5,0.1,2.4,0.1c1.2,0.1,2.4,0.2,3.5,0.2c2,0,3.3-0.3,3.9-0.9c1.2-1.2,3.8-2.1,5.3-2.5l1.1-0.3l0.2,1.1c0.2,1.4,0.6,4.9,0.9,7.2c0.1,0.9,0.1,1.8,0.1,2.7c-0.1,1.8-0.1,3.6,1.2,5.6c0.8,1.2,1.9,2.2,2.9,3.1c1.7,1.5,2.2,2,2.2,2.7l0,0.2l-0.1,0.2c-0.1,0.2-0.2,0.3-0.4,0.4c-0.6,0.5-2.1,1.6-1.9,2.4c0.1,0.2,0.4,0.6,1.4,0.8c2.7,0.6,4.9,1.5,6.5,2.1l0.5,0.2c1.6,0.6,3.8,2.4,3.8,3.9c0,1.1-0.4,4.5-0.6,5.9l-0.1,0.6l-0.6,0.2c-0.6,0.2-2,0.8-3.5,1.5c-1.2,0.6-2.2,1.8-2.4,2.8c-0.1,0.6,0.1,1.1,0.4,1.4c1.2,1.2,3,4.1,3.3,4.7c0.1,0.2,2.1,3.8,2.1,5.5c0,1.3,0.7,4.1,1,5.2l2.8,2.8l2.8,1.4l2.7,3.7l0.4,0.3l-0.7,1.8c0,0,0.1,0,0.1,0c-0.2,0.1-4.4,2.4-5.7,2.7c-2,0.5-3.4,1.2-3.9,1.9c-0.6,0.9-3,3.7-5.8,4.4c-0.7,0.2-1.4,0.3-2.1,0.3c-2.2,0-4.5-0.8-6.7-2.3c-0.6-0.4-1.4-0.6-2.2-0.6c-2.6,0-5.3,2.1-5.8,2.6c-1.1,1.1-6.8,3.7-8.8,4.4c-2,0.7-3.6,1.6-4.9,2.9c-0.3,0.3-0.5,0.7-0.8,1.1c-1,1.7-2.5,4-8.1,4.3c-5.8,0.3-8.3,6.4-8.9,8.3l-0.2,0.7l-0.7,0c-1.1,0-3.9-0.1-6.5-0.7c-0.5-0.1-0.9-0.1-1.3-0.1c-1.3,0-1.7,0.5-2.2,1.7c-0.1,0.3-0.2,0.5-0.3,0.7c-0.5,1-1.6,2.3-2.3,3l-0.5,0.6L212,235.1z"
}, {
  id: "b4",
  parentId: "a1",
  name: "azerbaijangharbi",
  persianName: "آذربایجان غربی",
  persianNickName: "آذربایجان غربی",
  ltrRotate: 70,
  ltrX: 160,
  ltrY: -30,
  d: "M129.1,290.2l-0.7-0.6l-2-0.7l-1.2-0.3H124l-1.8,0.8l-1,0.3l-1.2,0.8l-1.7,0.5l-1.7-0.3l-1.5-1.4l-0.6-1.6l0.5-1.9l0.8-1.5l0.6-1l0.2-0.9l-0.6-1l-1.9-2.3l-0.4-1.9l0.2-3.2l-0.2-0.8l-0.7-0.6l-1.3-0.9l-0.7-1.8l1.1-0.7l-0.5-0.6l-0.5-1.5l-0.1-3.1l-0.3-1.5l-0.5-1.5l-0.7-0.7l-0.9-0.1l-3.1,1.2l-2.1,0.2l-2.1-0.9l-1-1.1l-0.3-0.9l-0.1-0.7l-0.2-0.6l-0.4-0.5l-0.6-0.5l-0.5-0.9l-0.1-0.8l-0.4-0.5l-1.2-0.9l-1.1-1.5l0.2-1.8l0.6-0.7l0.5-0.1v-0.9l0.7-2.6l1.2-2.4l0.1-0.9l-0.6-1.3l-1.4-2.3l-0.6-0.9l-0.6-0.3h-0.7l-1-0.3l-0.9-0.6l-0.5-0.6l-0.4-0.3l-0.5-0.1l-1.9,0.1l-1.8-0.5l-1.6-0.9l-0.8-1.9l0.9-2.2l2.2-2.5l0.7-1.1l0.2-1.2l-0.2-1.3l-0.5-1l-0.5-1.5l0.4-2.5l0.7-0.7l0-0.1l0-0.1l-1.2-0.6l-0.6-0.7l0,0l-0.1,0l-1.4,0.3l-1-0.2l-0.7-0.7l-0.3-1.3l0-0.1l-0.1-0.1l-0.3-0.1l-0.7-0.2l-0.6-0.9l-0.6-1.5v-1.1l0.9-2.2l0.3-0.9l-0.3-0.8L82,206l-0.3-1.8l0.7-1.7l1-0.8l0.7-0.4l0.4-0.5l0.1-1.5l-1-1.1l-3.4-2.1l-0.7-1.2l-0.4-0.9l0,0l-2,0.3l-1.1-1.1l-0.8-1.9l-0.4-0.3l-2.1-0.2l-1.4-0.7l-0.5-1.9l0.7-2l-0.2-0.9l-0.3-1.5l0.1-1.9l0.4-1.8l0.4-1.2l-0.1-0.6l-1-0.8l-1.6-1.6l0.4-2.8l0.6-0.9l2.1-1.5l0.2-0.4l0,0l-1.9-2.2l-1.3-1.1l-1.3-0.6l-1.2,0.1l-0.6,0.3l-1.2,0.5l-1.6-0.2l-0.7-1.5v-0.7l0.1-0.5l-0.1,0l-1.1-0.2l-0.9-1.2l-0.5-1.1l-0.2-0.8l-0.1-0.2l-0.4-0.3l-2-0.9l-0.4-0.1l-3.8,0.5l-2.6-0.5l-1.5-2.2l0.4-1.4l0.7-0.8l0.3-0.5v-0.5l-0.3-1l0.1-1.3l0.5-1.1l0.4-0.6v-0.1l0.7-1.2l1.4-1.5l0.4-1l0.5-1.4l0.7-1.1l0.9-0.8l0.8-0.3l-0.3-0.9l0.2-1.2l0.9-0.7l0.8-0.3l0.2-0.3l0.4-0.9l0.3-1.1l0.2-1.2l-0.3-3.7l2.1-2.1l2-1.6l1-1.3V127l-0.3-0.8l-0.6-0.8l-0.6-0.4l-0.5-0.2l-0.4,0l-2,1.1l-3.3-0.6l-1.1-0.4l-0.9-0.7l-0.4-1.1l0.2-1.3v-0.5l-0.1-1.7l0-1l0.7-2.8l0.1-1l-0.6-3.5l0.3-2.8v-1.3l-0.3-0.7l-0.2-0.2l-0.3-0.2l-1-0.3l-1.8-0.9l0.7-1.4l0.5-0.5l0,0l-0.2-0.8l-0.3-0.9l-0.1-1l0.2-1.6l1.6-4.9l-0.2-1.2l-2.8-1.3L50,90.3l-0.9-1.2l-0.7-1.6l-0.2-0.7l-0.3-0.6v-0.9l-0.7-0.6l-0.6-0.8l-0.2-1.2l-0.1-0.3l-0.6-1l1.2-2l1-0.7l0.2-0.4l-0.5-2.6l0.4-1.4l1-1.9l-0.2-0.9l-1.9-1.2l-2.6-1.3l-1.9-1.4l-0.2-1.2l0.4-1.3v-0.2l-0.6-1.3L41.6,63v-0.9l0.1-0.5v-0.1l-0.7-1.2l-0.3-1.5l-0.2-0.4l-1.5-1.6L38.4,55l1.2-1.4l1.4-0.8l1-0.4h1.2l1.2,0.1l1.2-0.1l3.3-0.8l1.7,0.2l4,1.8l1.2,0.1l1.1-0.2l2.8-1.1l1-0.6l0.6-0.9l0.1-0.9l-0.2-1.3l0.3-2.5H62l0.1-0.2l0.1-0.4L62,44.6l-0.1-1.1l0.1-1.4l0.2-1.1l2-3.6l0.3-0.8l0.2-0.8l-0.3-2.3l0.3-1.3l6.7-4.9l2-0.6l1.5,0.8l1.7,2.4l0.6,0.6l3.4,1.4l1.2,1l4.9,3.3l0.1,0.1l0.7,0.3l1.2,0.2l2.9,0.2l-0.7,1.1l0.6,0.4l0.9,1.8L94,47l0.6,1.1l1.7,1.4l-0.5,1l1,0.7l0,0h0.5l1,0.2l0.5,0.8l0.1,0.2l2.1,1.3l0.5,0.7l0.2,0.5l0.4,0.6l0.4,0.4L103,56l0.7,1l1.4,2.9l0.5,0.7l0.5,0.9l0.6,3.6l0,0.1l1-0.3l5.8,1.7l0.3-0.2l0.9-0.4l1.5,0.3l0.3,1.2l-0.1,0.6l0.7,0.2l1.2,0.6l0.6,1.6l-0.5,0.9l0,0l0.9,0.5l0.8,0.8l0.3,0.7l0.5,1.5l0.2,0.3l0.2,0.2l1.5,0.7l0.7,0.9l-0.2,1.3l-0.3,0.6l-0.2,1.4l-1-0.3c-1,0.8-3,2.6-4.6,3.9c-1.9,1.6-2.2,4-2.6,6.3l0,0.2c-0.3,2.3-0.3,6.9-0.3,8.6c0,1.6,0,4.9,1.3,6.9c0.9,1.4,2.4,4.2,2,5.9c-0.1,0.5-0.4,0.9-0.8,1.1c-0.6,0.4-1,0.7-1.5,1.1c-0.8,0.7-1.6,1.4-3.6,2.2c-2.7,1.2-7,2.9-7.9,3.3v5.5c0,0.9,0.7,3.1,1.3,4.8l3.7,6.7l17.3,45.2l10.1,15.1c1.8,2.2,5.8,6.6,8.1,6.8c1.6,0.2,3.4,0.6,5,1c1.4,0.4,2.7,0.7,3.3,0.7c1.3,0,5.9,2,6.2,4.2c0.4,2.6,0.7,4.5,0.7,5.4c0,0.1,0,0.3,0,0.5c-0.1,1.3-0.4,3.3,3.2,5c2.4,1.1,4.4,1.7,6,1.7c1.4,0,2.4-0.4,3.1-1.3c0.3-0.4,0.7-0.9,1.1-1.4c1.5-2,3.5-4.7,5.6-4.7c0.2,0,0.4,0,0.6,0.1c1.5,0.4,4.7,1,7.6,1c1.7,0,3-0.2,3.9-0.6c2.1-1,4-2.5,4.7-3.1l0.4-0.3l9,2.1l-0.4,1.1c-0.3,0.9-0.9,3.2,1,5.3c0.7,0.7,1.3,1.3,1.8,1.8c1.6,1.6,2.4,2.4,1.3,3.8c-0.7,0.9-1.3,2.1-1.6,3c-0.2,0.8-0.3,2,0.5,2.6c1.4,1.2,4.4,2.8,5.1,3.2c0.6-0.6,2-2.1,2.5-3.1c0.1-0.2,0.2-0.4,0.3-0.6c0.4-0.9,0.8-2,2.6-2c0.4,0,0.9,0.1,1.4,0.2c2.6,0.5,5.4,0.6,6.4,0.7l0.7,0l0.2,0.7c0.8,2.4,2.7,8.1,3.5,10.1c1,2.5,3.5,11.6,4,14c0.5,2.7,0.5,7.7-1,10.2c-1.6,2.6-6.6,5.1-10.2,5.1c-4.1,0-6.8-1.3-7.2-3.7c-0.4-2-1.7-2.2-4.3-2.6c-0.3,0-0.6-0.1-1-0.2c-3-0.5-4.6-1-6.2-3.6c-1.2-1.9-3.1-2.9-5.8-2.9c-0.8,0-4.5,0.5-8.8,1.2c-5.7,0.9-12.2,1.8-14.2,1.8c-3.2,0-5.7-0.3-6.2-4.2c-0.3-1.8-1.1-2.1-2.5-2.1c-0.6,0-1.2,0.1-1.8,0.1c-0.8,0.1-1.6,0.2-2.5,0.2c-3,0-6.4,0.8-7.3,0.9v7.8c0,1.9-0.3,5.1-2.2,5.7c-1.4,0.5-5.9,0.5-10.6,0.5c-2.6,0-4.3,2.1-4.3,5.3c0,3.1-0.6,3.8-3.3,3.8c-2.5,0-3.8,3-3.8,4.3c0,1.4-0.4,6.1-0.5,7l0.5,2.7L129.1,290.2z"
}, {
  id: "b5",
  parentId: "a1",
  name: "bushehr",
  persianName: "بوشهر",
  persianNickName: "بوشهر",
  ltrRotate: 65,
  ltrX: 880,
  ltrY: -95,
  d: "M549.3,890l-3-1.4l-4.7-2.2l-1.6-1.8l-0.1-2l0.8-1.5l1.5-0.6l1.4-0.1l1.2,0l0.9-0.1l0,0l-0.2-0.8l-0.6-0.6l-2.4-0.9l-1.1-1l-0.6-1l-0.9-2.3l-0.3-0.5l-4.3-4.6l-1.8-1.5l-2-0.9l-10.4-2.4l-2.4-1.3l-6.9-6.7l-2.1-1.4l-2.2-1l-2.5-0.4l-4.1,0.6l-1.4-0.4l-1.1-0.8l-1.1-0.3h-2.6l-3.4,0.8l-1.4,0.1l-6.6-0.5l-1.2-0.3l-0.6-1l-0.1-0.7l-0.1-0.3l0,0l-1.5-0.5l-1.4-1.2l-2.8-3l-0.8-1.1l-0.7-1.5l-0.2-1.7l-0.4-0.6l-1.1-0.5l-2.8-0.8l-1.4-1l-4.2-4.2l-0.7-0.9l-0.3-1.3l-0.1-2.1l1.3-3.7l-0.1-1.5l-1-1.7l-2-1.9l-0.8-1l-2.1-3.4l-1.9-2.1l-0.6-0.9l-3.6-9.4l-0.5-2.4l-0.1-8.8l-0.6-2.8l-1.2-2.3l-1.3-1.6l-1.6-1l-2.3-0.5l-2.4-0.2l-1.5-0.4l-0.8-1.1l-0.5-1.4l-2.7-3.6l-0.6-1.5l-0.3-2.1l0.3-2.3l2-1.4l1.7,0.8l1.4,1.2l0.2,0.3l0,0l0.6-0.8l1.1-1l0.2-0.5l0.2-1.2l-0.2-1.3l-0.1-0.1l-1.3,0.4l-0.7-2.9l-0.2-0.4l-0.1-0.1l-0.3,0.2l-1.3,0.3l-0.7-1.1l-0.1-1.4l0-0.1l-0.7-0.1l-4.4,0.2l-0.8,0.2l-1.6,1.1l-2.3-0.3l-1.8-1.6l-0.6-2.3l-0.2-1.9l0.3-1.1l0.6-1l0.4-0.8l0.5-1.4l1.5-1.3l0-0.4l-0.6-0.6l-1-1.8l0.5-2v-2.5l-0.3-2.6l-0.5-1.7l-0.6-1.2l-0.4-0.5l-1.8,0.3l-0.3-0.7l-1.6-2.4l-3.1-2.6l-0.6-1.1l-0.4-1.2l-0.8-1.1l-1.7-1.8l-3.6-1.4l-0.8-1.1l-0.4-1.4l-0.7-1.1l-1.6-1.8l-1.7-2.5l-2.6-5l-1.3-2l-0.9-0.9l-2.5-1.5l-2.4-2.6l-0.3-0.5l-0.3-1l-0.1-1.3l-0.5-1.7l0.1,0l0,0l0.8-2.9l-1.4-3.9l0.3-1.5l-0.5-0.4l-1-1.4l-1.3-2.3l1.5-0.2c0.1,0,2.4-0.4,2.7-2.8c0.3-2.3,1.2-5.2,2.1-5.9l0.7-0.5l0.6,0.6c0.7,0.7,1.7,1.5,2.8,2.3l0.1,0.1c0.8,0.7,1.8,1.4,2.8,2.3c2.3,2,4.5,2.9,4.6,3l5.9,2.2l0.1,0.6c0.2,2.2,0.7,6.3,1.8,8.3c0.8,1.5,1.3,2.9,1.7,4.1c0.4,1.2,0.7,2.1,1.2,2.6c0.6,0.6,2.4,1.4,3.8,1.9l0.1,0l0.1,0.1c0.5,0.3,3.1,2.1,3.5,4.9c0.1,0.8,0.1,1.6,0,2.1c-0.1,0.7-0.1,1.2,0.2,1.5c0.4,0.5,1.7,0.7,4.1,0.7c2.3,0,4.7-0.2,7.1-0.4c2-0.2,4.1-0.3,5.7-0.3c2,0,3.2,0.2,3.8,0.7c1.3,1,6.2,2.2,9.9,2.9l0.7,0.1l0.1,0.7c0.2,1.3,1.4,7.7,1.4,9c0,1.4,1.9,4.3,5.8,4.8c4.1,0.5,10.7,4.6,12.2,7.1c1.4,2.3,4.4,6.9,7,9.5c1.1,1.1,3,5,6,11.2c2.9,6.1,6.2,12.9,8,14.8c3.3,3.3,3.1,8.1,3.1,10.2c0,0.2,0,0.4,0,0.5c0,1,2.7,10.1,4.8,17.4l0.1,0.3c1.6,5.5,2.9,10.2,3.1,11.2c0.5,2.4,4,11.4,7.4,13.8c1.4,1,3.3,1.9,5.1,2.8c2.9,1.4,5.5,2.7,6.5,4.3c0.6,0.9,1.7,2.2,2.9,3.6c2.9,3.3,4.1,4.9,4.1,6c0,1.9,0.5,9.4,2,11.9c1.2,2.1,6.7,7.3,8.5,9l0.1,0c2.6,1.3,5.9,3.4,7.6,5.5c0.7,0.8,1.1,1.6,1.6,2.3c0.6,1,1.2,1.9,2.2,2.7c0.6,0.4,1.2,1.3,2,2.4c0.6,0.9,1.3,1.8,1.9,2.6l1,1.1l-12.8,4.4l-0.2,1.4L549.3,890z"
}, {
  id: "b6",
  parentId: "a1",
  name: "chvab",
  persianName: "چهارمحال و بختیاری",
  persianNickName: "چ و ب",
  ltrRotate: 50,
  ltrX: 680,
  ltrY: 35,
  d: "M446.3,620.5c-2.9,0-4.8-4.2-6.3-8.2c-1-2.6-1.9-2.6-2.5-2.6c-0.4,0-0.9,0.1-1.3,0.2c-0.6,0.1-1.2,0.3-1.9,0.3c-2.7,0-5.1-1.6-7.5-5.1l-0.5-0.7c-1.7-2.4-1.7-2.4-3-3.1l-0.4-0.2c-0.4-0.2-1-0.3-1.6-0.3c-2,0-4.5,1-6.2,2c-1.6,0.9-2.9,1.5-4.1,1.5c0,0,0,0,0,0c-0.7,0-1.3-0.2-1.8-0.5c-1.4-0.9-5.1-3.2-5.8-3.7l-0.8-0.5l0.4-0.8c0.9-1.8,4.6-6.5,7.7-10.3c-0.6-1.1-1.9-3.1-2.8-3.8c-1.4-1-3.7-3.4-5-4.7c-1.3-1.3-0.3-7.5-0.1-8.7c-1.6-1.5-7.2-6.4-8.9-7.5c-2.1-1.4-7.9-7.6-9.4-9.4c-1.8-2.1-3.7-7.5-3.4-9.2c0.1-0.3,0.1-0.6,0.2-0.8c0.4-1.3,0.7-2.4-1.1-3.9c-1.2-1-3.2-3-5.2-5l-0.1-0.1c-1.9-1.9-3.9-3.9-4.7-4.6c-0.7-0.5-2-1.7-3.5-3.1l-0.1-0.1c-2.3-2.1-5.1-4.6-6.7-5.8c-1.2-0.9-2.7-3-4.6-6.3l-0.7-1.2l1.4-0.3c0.5-0.3,3.4-1.7,5.2-2.9c1.6-1.1,5.5-3,7.2-3.8l0.9-0.4l0.5,0.8c0.3,0.6,0.7,1,1.1,1.4c1.2,0.9,3.6,2.4,5.7,3.7l0.3,0.2c2,1.2,3.7,2.3,4.3,2.8c0.2,0.1,0.4,0.3,0.6,0.5c0.8,0.7,2,1.6,3.3,1.6c0.7,0,1.4-0.2,2.2-0.7c1.4-0.9,2.8-1.4,4.2-1.4c1.6,0,3,0.6,4.1,1.8c2.1,2.1,6.3,5.7,7.6,6.3c0.1,0,0.2,0.1,0.4,0.1c1.6,0,4.9-2.3,6-4c0.2-0.4,0.5-0.8,0.7-1.2c1.1-1.9,2.3-4.2,5.3-4.2c0.2,0,0.3,0,0.5,0c0.3,0,0.6,0,0.9,0c2.7,0,5.7-0.8,8-1.5c1-0.3,1.8-0.5,2.4-0.6c0.5-0.1,1-0.3,1.6-0.5c0.9-0.4,1.8-0.7,2.6-0.7c1.1,0,2,0.5,2.7,1.6c1,1.5,1.7,3.1,2.4,4.7c0.7,1.7,1.4,3.2,2.2,4.2c1.5,1.8,2.8,4,1.4,6.6c-0.7,1.3-1,3.7-0.1,5.7c0.7,1.6,1.9,2.5,3.6,2.9c4.8,1,7.5,1.7,8.2,4.5c0.7,2.8,2.4,4.9,4.5,5.5c2.4,0.7,5.8,3.4,6.8,5.5c1,1.9,1.6,7.9,1.7,8.7l0,0.1c0.3,0.8,2.5,6.3-1.1,8.6c-4.3,2.7-3.9,5.6-3.6,6.7c0.3,1,0.1,4.7-1.1,13.9c-0.3,2.4-0.5,4.4-0.5,4.9c0,0.6,0.6,4.7,1.2,9l0.1,0.5c0.5,3.1,1,6.6,1.4,9.7l0.2,1.4l-5.8-1c-0.4,0.1-2.1,0.4-3.2,1.3c-0.4,0.3-0.8,0.8-1.2,1.3c-0.9,1.2-2.1,2.6-4.2,3.1C446.8,620.5,446.6,620.5,446.3,620.5z"
}, {
  id: "b7",
  parentId: "a1",
  name: "fars",
  persianName: "فارس",
  persianNickName: "فارس",
  ltrRotate: 0,
  ltrX: 555,
  ltrY: 760,
  d: "M611.6,905.7c-1.3-0.6-4.4-2.3-6.4-3.6c-1-0.7-2.3-1-4.1-1c-0.8,0-1.6,0.1-2.3,0.1c-0.8,0.1-1.5,0.1-2.3,0.1c-3,0-4.8-1.7-6.5-3.4c-1.1-1.1-2.7-2.1-4.4-3.1c-0.8-0.5-1.6-1-2.3-1.5c-2.4-1.6-12-5.4-15.4-5.4c-2.4,0-4.3-2.7-5.8-4.9c-0.7-1-1.3-1.9-1.9-2.3c-1-0.8-1.6-1.7-2.3-2.8c-0.4-0.7-0.9-1.5-1.6-2.3c-2-2.5-6.2-4.7-7.4-5.3l-0.1-0.1l-0.1-0.1c-0.7-0.7-7.2-6.7-8.6-9.1c-1.5-2.6-2-9.9-2-12.1c0-1.1-2.2-3.6-4-5.6c-1.3-1.4-2.4-2.8-3-3.7c-0.9-1.4-3.6-2.8-6.2-4.1c-1.9-0.9-3.8-1.8-5.2-2.9c-3.6-2.6-7.1-11.6-7.6-14.2c-0.2-1-1.7-6.1-3.2-11.5c-3.1-10.9-4.8-16.6-4.8-17.5l0-0.6c0-2,0.2-6.7-2.9-9.8c-1.9-1.9-5.1-8.5-8.1-14.9c-2.5-5.1-4.8-10-5.9-11.1c-2.6-2.6-5.6-7.2-7-9.5c-1.4-2.4-7.8-6.4-11.8-6.9c-4.1-0.5-6.2-3.6-6.2-5.2c0-1-0.7-5.4-1.5-9.3c-1.2-0.2-8.5-1.6-10.4-3c-0.6-0.4-1.7-0.6-3.5-0.6c-1.5,0-3.5,0.1-5.7,0.3c-2.4,0.2-4.8,0.4-7.1,0.4c-3.1,0-4-0.3-4.5-0.9c-0.4-0.5-0.4-1.1-0.3-1.9c0.1-0.6,0.1-1.2,0-2c-0.2-1.2-0.8-2.3-1.9-3.4l-0.6-0.6l0.5-0.6c0-0.4,0-2,1.1-3.1c0.7-0.7,1.7-1.1,3-1.1c0.2,0,0.5,0,0.8,0c0.6,0.1,1.2,0.1,1.8,0.1c2.6,0,4.9-0.6,6.1-1.7c0.5-0.5,0.8-1.1,0.8-1.7c0-1.9,0.6-6,0.9-8.5l0,0l0.1-0.5c0.2-0.6,1.6-6.2,4.2-6.2c1.9,0,6.6-1.9,8.8-2.9c2.3-3.5,4.4-8.1,3.5-9.7c-1.2-2-3-7.4-4.3-11.2l-0.4-1.2c-0.8-2.3-1.4-4.6-0.6-5.7c0.3-0.4,0.8-0.7,1.5-0.7c2.8,0,4.5,1.3,6.2,4.6c1.5,2.9,5.4,6.4,8.3,6.4c0.7,0,1.5-0.1,2.3-0.1c0.8-0.1,1.7-0.1,2.5-0.1c1.3,0,3,0.2,3.9,1.3c1,1.3,2.7,2.7,4.7,2.7c0.5,0,1-0.1,1.5-0.3c2.4-0.9,4.3-3.4,4.3-5.3v-7.4l-1.2-6.5c0-0.4-0.8-8.7,0.7-11.2c0.7-1.2,1.3-3.6,2-6.2c0.7-2.6,1.3-5.1,2-6.3c1.6-2.7,5.4-12.5,5-15.8c-0.4-2.9-1.6-10.4-2-12.8l0-0.3l0.1-0.3c1-2.2,4.2-9.7,6.5-11.9c1.5-1.5,6.5-4.9,11-4.9c0.1,0,0.3,0,0.4,0c2,0.1,3.7,0.9,5,2.4c4.6,5.6,9,6.4,11.3,6.4c2.4,0,11,0.4,11.9,0.5l0.1,0l0.1,0c0.4,0.1,3.9,1.1,7.6,1.1c0.6,0,1.2,0,1.8-0.1l0.6-0.1l0.3,0.5c0.7,1,3.3,4.6,6.2,7.1c1.6,1.4,2.4,3,2.1,4.7c-0.2,1.4-1.3,2.7-2.7,3.2c-1.9,0.8-5.2,4-6.8,5.8l8.8,10.8c5.6,3.1,21.9,12.1,24.4,13c2.9,1,7.4,7.1,8.1,8c1.5,0.1,16,1,17.9,1c1.6,0,2.8,1.1,4.3,2.5c0.6,0.5,1.2,1,1.8,1.6c2.7,2.2,3.1,5,3.1,7.7c0,2.9,0.5,13.5,0.5,13.9l0,0.1l0,0.1c-0.1,0.7-0.5,6.6-2.1,8.2c-0.7,0.7,0.2,3.7,3,8.2l0.1,0.1c0.6,0.5,5.1,3.9,6.7,5.9c1.7,2.1,3,7.7,3,10.2c0,1.9,2.1,5,3.3,6.5l0,0.1l5.4,9.1c2.1-0.2,10.9-1.3,12.4-1.7c0.5-0.1,1.3-0.2,2.5-0.2c2.5,0,6.1,0.3,7.7,0.6c1.9,0.4,11.1,1.5,12.2,1.6l0.5,0.1l0.2,0.4c0.5,0.9,2.2,3.8,3.6,5.9c0.8,1.2,4.9,6.2,9.3,11.6l0.4,0.5c4.8,5.9,10.2,12.6,11.7,14.7c2.9,4.2,1.3,16.9,0.4,19.5c-0.4,1.1-0.2,3.8,0.6,7.2l0.1,0.5l-0.1,0.1l0.1,0.1l0.1,0.5c0.2,0.8,0.3,1.3,0.4,1.5c2.8,3.6,6.3,7.7,7.4,8.3c1.2,0.6,3.2,2.6,3.5,4.6c0.2,1.1-0.1,2.1-0.9,2.9c-2.8,2.8-2.9,6.5-2.9,7c0,0.6-0.3,6.9-0.6,13.9l-0.1,1.3c-0.3,6.1-0.6,11.9-0.6,12.5c0,1.2,2.1,4,4.1,5.2c1.3,0.8,2.5,3,3.6,5.1c0.7,1.3,1.3,2.6,2,3.4c1.8,2.2-0.4,5.3-2.5,8.3c-2,2.9-13.5,16.9-15.1,18.5c-1.7,1.7-6.3,4.3-8.1,4.3c-1.6,0-9.7-0.4-14.7-0.8l-2-0.2c-6.2-0.5-17.8-1.5-21.9-1.5c-3.1,0-5.9,0.6-8.8,1.2c-1.4,0.3-2.9,0.6-4.6,0.9c-4.5,0.8-13.2,6-14.8,6.9c0.6,0.7,1.9,2.5,3.2,4.4c1.7,2.5,0.2,4.6,0.1,4.8l0,0.1l0,0.1c-0.7,0.7-5.9,6.4-7.1,7.9c-1.2,1.6-6.7,3.9-7.3,4.1l-0.4,0.2L611.6,905.7z"
}, {
  id: "b8",
  parentId: "a1",
  name: "gilan",
  persianName: "گیلان",
  persianNickName: "گیلان",
  ltrRotate: 60,
  ltrX: 340,
  ltrY: -200,
  d: "M371.9,247.6c-1.8,0-3.5-0.7-5.3-1.5c-1.7-0.7-3.5-1.5-5.2-1.5c-3.8,0-7.8-2.7-9.2-4.6c-1.4-1.9-7.7-8.2-8.4-8.9l-0.1-0.1l-0.1-0.2c-1.5-3.5-4.3-9.8-5.4-11.3c-1.2-1.6-8.7-9.2-12.5-13c-0.3-0.2-3.1-2.2-3.1-5.7c0-3.4,0-6.4-1.4-8.4c-0.5-0.7-1.1-1.3-1.6-2c-1.1-1.3-2.2-2.7-2.9-4.1c-1.4-2.7-4.1-7.6-5.9-8.9c-2.2-1.6-2.6-4.8-1.1-7.8c1.5-2.9,0.5-5.4-1-8.3c-0.1-0.3-0.3-0.6-0.4-0.9c-1.5-2.9-3.4-6.5-0.5-8.9c3.1-2.6,3.9-6.6,3.9-8.3c0-1.9,0.9-9.3,1-10l-2.5-9.9l-0.8-1.6l1.9,0.1l1.2-0.4l1.4-0.5l1.3-0.8l1.2-1l1.6-0.9h2.3l4.7,1l0.2,7l-0.7,2l0.4,1.2l0.1,3.6l1.1,2.5l0.9,8.6l2.5,8.2L329,154v1.3l0.2,1.3l0.4,0.9l2.1,3.3v1.1l-0.1,0.8l-0.1,0.3l0.5,2.4l1.1,2.4l2.9,4l3.8,3.8l4.2,2.7l9.3,4.6l4.2,1.3l22.3,2.9l2.1-0.3l2-0.8l2.3-0.4l5.3,2.5l-1.5,0.3l1.4,0.5l7.6,1.6l2.9,1.1l2.4,2.2l-0.2,2.7l0.4,0.7l0.7,2.5l0.5,0.9l0.8,1.4l1.4,3.7l1.7,2.5l1.9,1.8l4.2,3l2.9,3.3l0.6,0.4l1.1,0.3l3.8,2.5l-1,0.8l-3,7c-0.7,1.5-3.1,6.7-4,8.9c-1,2.4-6.3,7-7,7.5l-0.4,0.6l-0.8-0.2c-0.6-0.2-1.2-0.4-1.8-0.7l-0.1,0c-2.7-1-4.7-1.7-5.9-1.7c-0.3,0-0.5,0-0.7,0.1c-0.4,0.2-1,0.5-1.7,0.9c-3.8,2-8.1,4.3-10.4,4.6C384.5,247.6,375.4,247.6,371.9,247.6z"
}, {
  id: "b9",
  parentId: "a1",
  name: "golestan",
  persianName: "گلستان",
  persianNickName: "گلستان",
  ltrRotate: -30,
  ltrX: 470,
  ltrY: 520,
  d: "M648.3,255.1c-0.3,0-0.7,0-0.9-0.1c-0.6-0.1-2.1-0.2-5.9-0.2c-3.8,0-8.2,0.1-10.5,0.2l-1.4,0l0.4-1.3c0.5-1.6,0.6-3.9-0.1-5.5c-0.4-0.9-0.9-1.4-1.7-1.7c-2.3-0.8-6.5-2.5-8.8-3.4l-0.1,0l0,0l-0.1-0.1c-0.1-0.1-3.1-1.6-3.6-3.7c-0.5-1.9-0.5-5.4-0.5-6l-1.5-2.9l3.3,1.8l0.6,0.2l6.9-1.8l0.3-0.3l0.2-0.7v-6.9l-0.2-0.6l-0.5-0.3l-1.8-0.7l0.4-2l1.1-2l-1.1-1.6l-1-2.8l-1.3-5.8l-1.8-4.4l-0.4-1.2l-0.6-7.2l17.1,1.4l0.9,0l0.7-0.3l0.9-0.9l1.4-0.9l1.7-0.1l1.3,0.2h1.1l1.9-0.5l10-5.4l1.7-0.2l3.6,0.7h1l0.5-0.2l1.4-1.5l1.2-0.4l0.6-0.6l2.9-1.8l1.3-0.9l0.1-0.1l0.1-1l0.8-1.7l0.2-0.8l0.1-1.5l0-0.2l-0.1-0.2l-0.7-0.6l-0.4-0.8l-0.1-1.9l1-2.3l0.2-1.2l0.4-1.3l0.9-1.4l1.8-2l8.8-5.6l2.6-2.7l0.3-0.5l0.4-1.2l1.3-0.7l0.8-0.1l0.3-0.1l0.2-0.3l0.7-1.2l0.8-0.9l1.4-0.4l3.4-0.6l0.2-0.1l0.5-1.1l1.7-0.8l2.8-0.9l0.4-0.1l1.1-0.8l1.3-0.6l4.3-3.1l1.7-0.6l3.9-0.2l11.5-2.3h2l3.8,0.9l2.4,1.2l0.6,0.2h3l1.2,0.4l1.6,0.8l0.6,0.2l0.7,0.1l8.4-1.4l2.8,0.2l0.4,0.3l1.6,0.6l0.6,0.1l4.6-0.7l1.7-1.1l1.8,8.8v8.1l-6,5l-1,8.5l-0.2,0.2c-1.5,2-6.7,8.7-8.9,10.9c-1.6,1.6-2.3,7.1-2.4,11.6l0,1h-6.7l-0.1,0c-0.5,0.1-3.6,1-5.4,2c-1.1,0.6-4.9,2.6-4.9,5.3c0,3.1-1.6,5.4-4.7,6.7c-2.2,0.9-2.8,6.2-2.4,10.9l0,0.4l-0.3,0.3c-0.8,1-5,5.9-6.4,6.8c-1.3,0.8-6.2,4.4-8.3,5.9l-0.3,0.2h-13.1c-4.5,0-10.7,1.7-13.3,6.4c-1.5,2.7-3.9,4.8-6.3,5.4c-0.5,0.1-1,0.2-1.5,0.2c-0.8,0-1.4-0.2-2-0.5c-0.4-0.3-0.8-0.4-1.1-0.4c-0.9,0-1.8,1-2.7,2c-0.7,0.7-1.4,1.6-2.3,2.3C658.7,253,651.7,255.1,648.3,255.1z"
}, {
  id: "b10",
  parentId: "a1",
  name: "hamedan",
  persianName: "همدان",
  persianNickName: "همدان",
  ltrRotate: -60,
  ltrX: -180,
  ltrY: 450,
  d: "M322.5,426.7c-1.7,0-4.8-0.9-5.7-2.2c-0.5-0.7-1.4-1.9-2.2-3c-0.9-1.1-1.8-2.3-2.3-3c-0.3-0.5-1.1-0.7-2.4-0.7c-0.8,0-1.7,0.1-2.5,0.2c-0.9,0.1-1.7,0.2-2.4,0.2c-3.3,0-4.9,1.1-5.3,3.8c-0.1,0.7-0.4,1.2-1,1.7c-0.8,0.6-2.1,0.9-3.9,0.9c-1.3,0-2.6-0.2-3.3-0.3l-0.1,0l-0.1,0c-1.1-0.4-6.7-2.7-9.5-4.5c-3.1-2.1-4.1-6.2-4.6-8.1c-0.2-0.7-0.7-2.8-5.8-2.8c-3.7,0-4.7-1.1-6.2-3.6c-1.2-1.9-0.2-4.1,1.1-5.3l3.9-4.4c2.6-2.6,4-4.7,4-5.4c0-1.3-0.4-5.1-0.5-6.3c-0.6-0.3-3.2-1.5-5.8-1.9c-2.9-0.5-4.4-1-6.6-2c-1.2-0.6-1.6-2.7-1.9-5.6c-0.2-1.4-0.3-2.8-0.7-3.5c-1.1-2.2,0.1-6.3,2.5-8.8c1.4-1.4,1.4-1.9,1.4-2.2c0-0.1-0.1-0.3-0.3-0.5l-0.7-0.6l0.6-0.8c0.5-0.6,3.1-3.7,7.3-3.7c0.4,0,0.8,0,1.1,0.1c2.2,0.3,4.1,0.4,5.6,0.4c0.7,0,1.3,0,1.7-0.1c0.3,0,0.5,0,0.7,0c0.4,0,1.1-1.2,1.1-4.8v-7.9c-0.6-0.6-4.7-4.7-5.3-6.3c-0.4-0.9-1.5-1.9-2.6-2.9c-0.8-0.7-1.5-1.4-2.1-2c-0.4-0.5-1-1-1.7-1.7c-2.2-2.2-4.1-4.1-4.1-5.8c0-0.8-0.5-2.1-1.1-3.3c-1.1-2.7-1.5-3.9-1-4.7c0.3-0.4,0.7-0.6,1.3-0.6c3.3,0,10.2-1,11.8-2.6c1.4-1.4,5.6-5.2,6.9-6.3l0.8-0.7l1.8,2.5c0.5,0.3,3.7,2,7.9,2.4c2.6,0.3,4.2,1.5,5.5,2.5c1,0.8,1.9,1.5,3,1.5c0.8,0,1.7-0.3,2.5-0.5c1-0.3,1.9-0.6,2.9-0.6c1.1,0,2,0.4,2.8,1.2c0.8,0.8,1.7,1.2,2.7,1.2c0.2,0,0.4,0,0.5,0c1.2-0.2,2.3-1,2.9-2.1c0.4-0.8,0.1-1.4-0.7-2.5c-0.6-0.8-1.3-1.7-1.3-2.9c0-0.4,0-1,0-1.6l0-1.2l1.2,0.3c2.4,0.5,6.6,1.6,8.1,2.3c2,1,7.9,4.9,11,7c2.8,1.9,2.7,3.7,2.7,5.5c0,0.2,0,0.5,0,0.7c0,0.9,0.4,1.6,1.1,2.1c0.4,0.3,1,0.5,1.6,0.5c0.5,0,1-0.1,1.5-0.3c0.7-0.3,1.4-0.4,2.2-0.4c1.7,0,3.1,0.8,4.1,1.5c1,0.7,3.6,1.9,5.6,2.9l0.1,0.1c0.6,0.3,1.1,0.5,1.6,0.7l0.9,0.4l-0.4,0.9c-0.7,1.6-2.6,5.5-4.2,7.9c-0.6,0.9-0.7,1.6-0.5,2.3c0.5,1.4,2.7,2.3,4.4,2.9c0.7,0.2,1.3,0.7,1.5,1.2c0.6,1.2,0,2.9-0.5,4.3c-0.2,0.5-0.3,0.9-0.4,1.3c-0.2,0.6-0.4,1.5-0.8,2.5c-0.7,2.2-1.7,5.2-1.7,6.9c0,2.7-3.2,4.3-8.8,4.3c-5.1,0-7.6,9.1-7.7,9.8c0.1,0.9,0.5,6.6,0.5,8.5c0,2.3-1.2,4.8-3.8,4.8c-1.2,0-1.6,0.8-2.2,2.6c-0.4,1.1-0.8,2.3-1.6,3.3c-1.6,2-1.2,5.6-0.9,6.8l2.5,8.5c1,2.9,3.4,8.9,4.9,10.9c0.6,0.7,0.7,1.6,0.4,2.5c-0.7,2-3.5,4-5,4.4c-1.3,0.3-3.2,1.1-4.8,1.7c-0.9,0.4-1.7,0.7-2.2,0.8C323.2,426.7,322.9,426.7,322.5,426.7z"
}, {
  id: "b11",
  parentId: "a1",
  name: "hormozgan",
  persianName: "هرمزگان",
  persianNickName: "هرمزگان",
  ltrRotate: 0,
  ltrX: 735,
  ltrY: 870,
  d: "M922.6,1021.8l-0.6-0.6l-0.5,0.2l-0.9,0.3l-1.6-0.1l-1.3-0.3l-1.3-0.5l-0.9-0.9l-2.7-4.7l-1.3-1.7l-1.9-0.9l-2,0.1l-1-0.6l-0.6-1l-0.2-0.7l0,0l-0.2-0.1h-5l-10.5-2.1l-3.6,0.6l-3.4-0.2l-2-1.1l0.2-0.5l-0.1,0l-1.6,0.3l-0.6,0.4l-1.4,1.3l-1.5,0.3l-0.5-0.3l-0.3,0.3l-0.7,0.4l-1,0.3l-1-0.2l-1.7,1.3l-2.5,0.4l-2.2-0.4l-1.8-0.6l-2-0.3l-2-1l-1.5-2.2l-1.8-3.9l-1.5-2l-1.6-0.4l-2,0.5l-2.2,1.2l-2,1.8l-1.6,1h-2.3l0.4-4.2l0.3-1.4l0-0.2l-0.5-1.3l-0.5-0.5l-0.9-0.2l-1.3-0.1l-1.2,0.1l-3.4,0.8l-1.1-0.2l-1.2-0.7l-0.4-0.1l-0.5,0.1l-1.1,0.3l-0.8,0.1l-1.7-0.2l-5.7-1.9l-5.8-0.4l-1.3-0.8l-0.6-1.4l-0.4-3.4l-1.4-3.4l-0.7-2.8l-0.4-1l-0.6-0.6l-0.1-0.4l-0.9-1.1l-0.4,0.1h-1l-0.3-1l-0.2-0.9l-0.8-2.5l-0.2-1.1l-0.6-1.3l-0.1-1.1l0.4-1.9l2-2.2l0.4-0.9l-0.6-1.7l-4.1-4.7l0.3-1.8l-0.3-0.4l-0.3-3.3l-0.3-1.3l-0.6-1.1l-1.1-1.1l-0.4-0.8l-0.3-0.8l-0.2-1.7v-0.8l1-8.6l-0.2-3l-3.7-15.8l-0.6-1l-2-1.8l-1-1.5l0.1-0.9l-1.4-1l-2.4-2.8l3.1,0.4l0.4-0.2l0.3-0.2l0-0.2l-0.9,0.1l-1.2-0.2l-0.5-0.7l0-0.1l-0.2-0.1l-0.5-0.5l-0.1-0.1l-1.2,0.6l-1-1l-0.2-0.6l-0.1,0l-1.1-0.8v-1.6l1.1-0.5l0.1-0.1l0.5-0.6l-0.4-0.1l-1.7-1.2l-1.2-1.7l0-0.2l-0.6,0.2h-2l-1.2-0.5l-0.8-0.9l-0.3-0.4l-0.2-0.1l-6-0.1l-0.8-0.2l-0.5,0.7l-2-1.3l-1.5-0.3l-3.6-0.2l-1.9-0.4l-3.1-1.3l-1.6-0.3l-3.4,0.2l-1.6,0.4l-1.2,0.9l-1.6,0.9l-3.9,0.1l-1.3,0.3l-0.2,0.1l-0.8,0.8l-0.1,0.1l-0.1,1l-0.8,0.6l-0.5,0.1l-0.3,0.2l-1,0.9l-3.9,2.5l-1.1,0.9v0.4l-0.7,0.4l-1.1,1.1l-1,0.3l-2.7,0.4l-2.3,0.6l-0.8,0.1l-2-0.1l-0.2,0l-0.9,0.7l-0.8,0.2H725l-1.9-0.4h-0.2l-0.8,0.3l-1.9,1.9l-0.8,0.4l-0.5,0.5l-1.3,1.5l0.3,2.3l-0.4,2.3l-0.7,2.1l-1,1.6l-2.1,2l-2.4,1.3l-2.7,0.6l-3-0.1l-4.8-1.7l-2.3-0.3l-1.6,0.8l-0.5,0.9l-0.3,1.2l-0.9,1.5l-1.8,0.4l-1.1,0.2l-2.5,0.8l-0.7,0.3l-3.8,3.6l-0.7,0.4l-5.6,4.9l-6.3,3.9l-1.3,1.3l-1.2,0.3l-1.1-0.3l-0.9-0.6l-0.4-0.1l-5,0.4l-3.2-0.5l-1.3-2l-0.7-1.9l-1.3-1.4l-2.2-0.4l-5.4,0.2l-2.7-1.3l-1.2-2l-0.9-2.3l-1-1.9l-1.3-1.2l-0.8-0.1l-0.9,0.2l-1.2,0.3l-4.6,0.4l-1.5-0.2l-4.1-1.2l-1-0.2l-0.9-0.3l-1.1-1l-0.2-0.1h-0.3l-1.1,0.2l-3.8,1.9l-2.8,0.4l-2.4,0.7l-1.6,0.1l-2.7-0.9l-1-0.1l-1.6,0.9l-1.3-0.6l-3.1-2.9l-4.4-2.8l-5.8-4.6l-1.1-1.4l-0.4-1.6l-0.1-3.2l-0.4-1.1l-0.8-1l-1.7-1l-19.7-7l-1.2-0.2l-1.6-0.4l-1.1-1.2l-0.6-1.2l-0.5-0.6l-3.4-0.9l-0.9-1.1l-0.5-1.4l-0.8-0.5l-2.8-0.8l-5.5-5.3l1.8-0.5l0,0l11.9-4.1l0.7-0.3l0.4,0.4c0.9,0.7,1.6,1.1,2.4,1.1c3.3,0,13,3.7,15.7,5.5c0.8,0.5,1.5,1,2.3,1.4c1.7,1.1,3.3,2,4.5,3.2c1.6,1.6,3.3,3.3,6.1,3.3c0.7,0,1.6-0.1,2.2-0.1c0.8-0.1,1.6-0.1,2.4-0.1c1.3,0,2.9,0.1,4.4,1.1c2.3,1.5,5.9,3.4,6.6,3.7c3-1.2,6.5-3,7.3-4.1c1-1.3,4.9-5.5,7.1-7.9l0.1-0.1c0,0,1.5-2-0.1-4.3c-1.1-1.7-2.3-3.2-2.8-3.9l-0.7-0.9l1-0.6c3-1.8,10.3-6,14.5-6.7c1.7-0.3,3.2-0.6,4.5-0.9c3.1-0.7,5.8-1.2,8.9-1.2c4.1,0,15.7,1,21.9,1.5l2.1,0.2c5.1,0.4,13,0.8,14.7,0.8c1.5,0,6.1-2.4,7.8-4.1c1.7-1.7,13-15.5,15.1-18.4c2.5-3.5,4-5.9,2.5-7.7c-0.7-0.8-1.3-2.1-2-3.4c-1-2-2.2-4.2-3.4-4.9c-2.2-1.3-4.3-4.3-4.3-5.7c0-0.6,0.3-6.6,0.6-13.9l0.1-1.8c0.3-5.9,0.5-11.5,0.5-12.1c0-0.4,0.1-4.4,3-7.3c0.7-0.7,0.9-1.5,0.8-2.4c-0.3-1.8-2.1-3.7-3.2-4.3c-1.7-0.8-6.9-7.6-7.5-8.3l-0.1-0.2l-0.1-0.2c-0.1-0.3-0.2-0.7-0.3-1.1l-0.3-1.2l1.2,0c0.2,0,0.4,0,0.6,0c2,0,4.8,0.4,6.4,2.3c1.3,1.5,2.8,2.3,4.5,2.3c1.2,0,2.5-0.4,4-1.1c1.8-0.9,4.3-2.2,6.5-3.4l0.2-0.1c1.8-1,3.5-1.8,4.6-2.4c0.5-0.2,1-0.5,1.6-0.8c2.7-1.4,6-3.1,7.7-3.4c1.8-0.4,4.6-1,5.4-1.2l0.1,0l4.5-0.5l-0.1,1.2c-0.2,1.9-2,19-2.4,20.5c-0.4,1.7-1.2,14.2-0.4,16.2c0.7,1.8,2.7,5.7,5.4,7.9c0.3,0.3,0.7,0.6,1.1,0.9c2.5,2.1,6.3,5.4,8.4,5.7c1.7,0.3,4.5,0.4,8.3,0.4c0.6,0,2.5-0.1,4.6-0.2l0.1,0c2-0.1,3.9-0.2,4.5-0.2c1.2,0,4.4-1.2,4.8-2.7l1.3-5.2l17.2-1.3l0.2,0.9c0.4,1.9,2.4,11.4,2.4,13.3c0,2.2,4.2,11.1,9.4,11.1c3.7,0,7.4,0.4,9.8,0.6c1.1,0.1,2,0.2,2.4,0.2c1.2,0,3.2,0.4,3.2,2.8c0,1.1,0.4,3.1,1.1,5.6l0.2,0.9l-0.8,0.3c-3,1.2-5.3,2.6-6,3.4c-0.5,0.7-1.6,2-4.1,4.6l-0.1,0.1c-1,1.3-2.5,3.9-2,5.2c0.2,0.5,0.7,0.9,1.5,1c4.1,0.8,4,3.6,4,5.6l0,0.5c0,1.2,0.4,4.2,0.7,6.6c0.3,2.4,0.5,3.8,0.5,4.3c0,1.3,1.7,5.7,5.6,6c4.2,0.4,6.9,3.3,7.3,4.8c0.1,0.3,0.1,0.7,0.2,1.1c0.2,1.8,0.6,4.2,3.4,5.4c4.1,1.8,5.7,4.2,6.8,6.4c1.2,2.5,1.6,3.2,5.6,3.2c0.5,0,1,0,1.5,0l0.3,0c0.6,0,1,0,1.5,0c2.3,0,4.5,0.1,6.1,1.8c0.7,0.7,1.4,1.5,2.2,2.3c1.7,1.8,3.5,3.7,4.9,4.8c1.6,1.2,6.1,3.5,9.7,3.5c0.5,0,1-0.1,1.4-0.2c1.1-0.3,2-0.5,3-0.5c1.6,0,3,0.7,5.2,2.6c2.5,2.2,2.7,3.5,3,4.8c0.1,0.5,0.2,1,0.4,1.6c0.7,1.7,4,3.6,6.7,5.1c0,0,0.9,0.5,1.2,0.7c0.3,0.2,0.7,0.4,1.1,0.6c2.7,1.6,6.1,3.6,8.3,3.6c0.2,0,0.3,0,0.5,0c0.1,0,0.1,0,0.2,0l0.2-0.1l1.1-0.3l0.2,1.1c0.8,4.3,2,9.9,2.8,11.6c0.5,1,1.6,3.6,2.8,6.6l0.2,0.5c1.9,4.6,4.3,10.4,5.3,12.1c1.8,3.2,0.7,4.2-1.8,5.8c-0.5,0.3-0.8,0.8-0.8,1.2c0,1.1,1.2,2.6,3.3,4.2c1.7,1.3,5.9,7.2,6.8,8.9l0.3,0.6c0.8,1.6,1.8,3.6,1.8,6.3c0,2.8-0.8,18.5-0.8,20.1l0.5,1.1l-1.9,0.3l-3.3,1.7l-1.5,0.4L922.6,1021.8z"
}, {
  id: "b12",
  parentId: "a1",
  name: "ilam",
  persianName: "ایلام",
  persianNickName: "ایلام",
  ltrRotate: 50,
  ltrX: 500,
  ltrY: 160,
  d: "M253.3,566.6l-0.4-1.5v0l-0.3-0.7l-1.9-0.9l-1.1-1.3l-1.3-3.1l-0.8-1.2l-0.6-0.2l-1.2-0.1l-0.8-0.9l-0.4-0.6l-0.5-0.3l-0.9-0.3l-0.9-0.7v-1.1l0.1-1.1l0.3-1l0.5-0.7l0.2-0.4l0.1-0.6l-0.1-0.4l-1.2-0.9l-0.3-0.7l-0.5-0.2l-0.4-0.6l-1.1-1.5l-0.2-0.4l-0.2-0.3l-1.7-1.7l-0.4-0.5l-0.5-1.2v-0.9l0.4-0.4l0.5-1.2l0.3-0.4l0,0l0-0.3l-0.1-0.2l-1.6-1.2l-1-1.4l-0.7-0.9l-0.7-0.7l-1-0.6l-3.1-1l-0.4,0l-2.5,1.4l-1.3,0.5l-2.3,0.2l-2.2-0.5l-1.9-1l-2-1.4l-17.8-15.4l-2.3-2.6l-3.7-2.3l-2.7-2.1l-5.8-3.3l-1.6-1.6l-5.7-2.7l-5.9-1.8l-6.8,0.8l-4.1-0.5l-1.8-3.9l1.3-1.5l0.9-0.7l0.7-0.7l0.2-0.7l-0.1-0.4l-0.6-0.4l-0.9-0.4l-2.8-0.3l-1.4-1.3l0.2-1.9l1.8-0.9l1.6-0.2l0.9,0.1l0.6-0.1l1-0.7l1.5-1.6l0.7-0.7l0.2-0.5l-0.4-0.3l-0.6-1.1l0.2-0.9l0.3-1.2v-0.4l-0.3-0.8l-0.6-0.6l-2-1.6l-2.3-3.2l-2.1-2l-0.4-1.4V468l-0.2-1.2l-0.5-1.2l-0.5-1l-1.8-2.2l-0.2-0.1l-0.1-0.1l-1.3,1.1l-2.3,0.3l-2.1-0.5l-1.9-1.5l1.6-2.1l2.8-1.7l0.3-0.5l-0.2-0.8l-1.1-0.7l-1.4-1.5l0.1-1.1l-2.8,0.1l-0.7,0.3l-1.6,1.5l-1.2,0.9l-1.8,0.4l-1-1.2v-2.6l-0.1-0.3l-0.1-0.3l-2.6-1.8l-2-2l1.6-0.5l0.3-0.1l0.3,0.1c0.7-0.3,5.7-2.8,8.2-4.9c1.2-1.1,2.1-2.3,2.8-3.2c0.9-1.2,1.6-2.1,2.6-2.5c1.1-0.4,2.6-1.7,3-2.9c0.2-0.5,0.1-1-0.1-1.4c-0.3-0.5-0.7-0.9-1.2-1.4c-1-1-2.2-2.2-2.2-4.4c0-0.7,0.1-1.8,0.8-2.4c0.6-0.6,1.5-0.6,2.3-0.6c0.6,0,1.3,0.1,2.2,0.1c0.3,0,0.7,0.1,1,0.1c3.5,0,4.5-2,4.8-2.6c0.1-0.3,0.2-0.7,0.3-1.1c0.3-1.3,0.5-1.6,0.7-1.8l0.3-0.4l0.5,0c0.3,0,0.9,0.2,1.9,1.5c2.1,2.6,5.8,4.7,8.2,4.7c0.3,0,0.6,0,0.8-0.1c0.6-0.2,1.7-0.5,3.1-0.5c1.9,0,3.6,0.7,4.9,1.9c1,1,3.2,2.9,5.6,4.9c3.1,2.6,6.6,5.5,7.7,6.8c1.3,1.5,4.1,1.7,6.5,1.9c1.2,0.1,2.3,0.2,3,0.4c0.4,0.1,1.1,0.2,1.8,0.2c2.3,0,4.8-0.6,6-1.4c0.5-0.3,0.8-0.6,0.8-1c0.2-1.1,0.6-1.9,1.3-2.3c0.4-0.2,0.8-0.3,1.4-0.3c0.6,0,1.2,0.1,2,0.4c2.2,0.8,8.5,3,11.2,3c2.7,0,5.4-2.4,5.4-4.1c0-2.2-0.4-4.3-1-5.2c-0.5-0.7-0.8-2.5-0.3-3.2l0.3-0.4c0,0,0.5,0,0.5,0c0.3,0,0.6,0.1,0.9,0.2c1.7,0.8,7.7,2.5,9.5,3l0.7,0.2l0,0.7c0,0.5,0,1.1-0.1,1.6c0.2,0.9,0.6,2.7,0.7,3.3c0,0.1,0,0.2,0.1,0.4c0.1,0.7,0.3,1.5-0.4,2.6c-0.5,0.8-1.4,1.3-2.1,1.8c-0.3,0.2-0.6,0.4-0.7,0.5c0,0.1-0.2,0.2-0.3,0.4l-0.1,0.1c-0.6,0.8-2,2.6-2,3l-0.1,0.3l-0.2,0.2c-0.5,0.5-2,1.3-3.8,2c-1.3,0.5-2.7,0.5-3.4,0.5c-0.8,0-1.8-0.1-2.3-0.4c-0.2-0.2-0.4-0.3-0.6-0.3c-0.5,0-1.2,0.4-1.9,0.8c-0.4,0.2-0.8,0.3-1.2,0.3c-0.7,0-1.4-0.4-1.7-0.6c-0.4,0.4-1.2,1.2-2.2,1.5c-0.4,0.1-1,0.2-1.7,0.2c-0.8,0-1.6-0.1-2.3-0.1c0.1,0.3,0.1,0.8,0,1.1l-0.1,0.4l-0.3,0.2c-0.3,0.2-1,0.9-2.1,2.2c0.1,0.7,0.3,1.4,0.4,1.6l0.1,0.1l0,0.2c0,0.1,0.1,0.4-0.2,1.2l-0.3,0.8l-1.9-0.3c0,0-0.1,0-0.1,0c-0.2,0-1.8,0-2.4-0.5c-0.3-0.2-0.6-0.5-0.8-0.7c-0.3-0.2-0.5-0.5-0.8-0.7c0,0-0.3-0.2-1.2-0.2c-0.8,0-1.7,0.2-2,0.2c-0.4,0.1-0.6,0.4-0.7,1c-0.1,0.3-0.2,0.7-0.4,1c-0.4,0.6-0.1,1.1,0.5,2c0.5,0.8,1.4,1.7,1.7,1.9l2.1,2l0,0c2.4,1.4,4.3,2.4,4.8,2.6c0.6,0.2,1.1,0.7,1.4,1.3c0.2,0.5,0.2,1.1-0.1,1.6c-0.6,0.9-0.3,1.3,0.3,1.9c0.4,0.4,2.2,1,4.2,1.3c0.5,0.1,1.4,0.4,1.7,0.6l0.2,0.1l0.1,0.2c0.3,0.4,2.6,2.2,3.1,2.5c0.6,0.4,1.2,0.7,1.8,1.7c0.1,0.1,0.2,0.3,0.2,0.4c0.4,0.8,0.7,1.3,1.5,1.4c0.6,0.1,2.4,0.8,6.9,2.7c1,0.4,1.7,0.8,2,0.9c1,0.4,1.9,1.7,2.2,2c0.4,0.1,1.9,0.7,2.3,1c0.5,0.4,1.9,2.4,2.2,3.2c0.3,0.8,1.2,1.3,1.3,1.4c0.1,0,0.2,0.1,0.3,0.2c0.8,0.4,1.5,0.7,1.8,1.2c0.3,0.4,1.4,1.2,2.1,1.7c0.3,0.2,0.5,0.4,0.7,0.5c0.2,0.2,1.7,0.8,5.4,2.2l2.5,0.3l0.1,0.1c0.4,0.2,2.3,1,2.9,1.6c0.3,0.3,0.6,0.7,0.9,1.1c0.3,0.4,0.5,0.7,0.7,0.9c0.2,0.2,0.9,0.6,1.6,0.9c0.6,0.3,1.3,0.6,1.8,1c0,0,3.5,2.2,4.3,4c0.4,0.8,1.8,1.3,2.9,1.5l0.4,0.1l1.5,2.3l1,2c0.1,0.1,0.5,1.1,0.5,1.6c0,0.3,0.3,0.8,0.5,1.2c0.1,0.2,0.2,0.4,0.3,0.5c0.2,0.4,0.3,0.9,0.3,1.3l0,0.4l-0.3,0.3c-0.1,0.1-0.4,0.4-1.2,2l-0.2,0.3l-0.3,0.1c-1.1,0.5-3.6,1.6-4,1.7c-0.2,0.1-0.5,0.3-0.6,0.7c-0.1,0.2-0.1,0.4,0.1,0.6c0.5,0.6,0.4,1.7-0.2,2.4c-0.2,0.2-0.5,0.5-1.8,0.5l0,0c-0.1,0-0.2,0-0.4,0l-0.8,1.3l0.9,1.1l0.9,1.4l0.3,2.4v6.8l-1.3,3.6l0,0.1c-0.7,2.4-2.1,6.7-2.4,8.1c-0.5,1.7-2.5,6-3.5,7.6c-0.7,1-2.2,2.1-3.7,3.2c-0.7,0.5-1.3,0.9-1.8,1.4c-1,0.8-2,4.3-2.6,7.3l-0.5,2.9L253.3,566.6z"
}, {
  id: "b13",
  parentId: "a1",
  name: "esfehan",
  persianName: "اصفهان",
  persianNickName: "اصفهان",
  ltrRotate: 0,
  ltrX: 495,
  ltrY: 480,
  d: "M485.8,650c-6.3-4.9-17.1-13.3-19.7-15.6c-2.9-2.6-4.4-6.5-4.4-11.5c0-1-0.2-3.3-0.7-6.9l0-0.3l0-0.1l-0.1-0.1l0-0.3c-0.5-3.3-1-7.1-1.5-10.6l-0.1-0.4c-0.9-5.7-1.3-8.5-1.3-9.1c0-0.5,0.2-2.2,0.6-4.9c0.6-4.9,1.6-12.3,1.1-13.6c-0.9-2.6,0.5-5.2,3.8-7.3c3.3-2.1,1.2-7.3,0.9-7.9l-0.1-0.1l0-0.1c-0.2-2.3-0.9-7-1.6-8.5c-1-1.9-4.3-4.6-6.5-5.2c-2.2-0.6-4.1-2.9-4.8-5.8c-0.6-2.5-3.1-3.1-7.8-4.2c-1.8-0.4-3.2-1.5-3.9-3.2c-1-2.2-0.7-4.8,0.1-6.2c1.1-1.9,0.7-3.7-1.3-6.1c-0.9-1.1-1.6-2.7-2.3-4.3c-0.7-1.6-1.4-3.3-2.4-4.7c-0.8-1.2-1.7-1.4-2.3-1.4c-0.8,0-1.7,0.3-2.4,0.6c-0.6,0.2-1.2,0.4-1.7,0.5c-0.5,0.1-1.3,0.3-2.3,0.6c-2.3,0.6-5.4,1.5-8.1,1.5c-0.3,0-0.7,0-1,0c-0.2,0-0.3,0-0.5,0c-2.7,0-3.8,2.1-4.8,3.9l-0.1,0.1c-0.2,0.4-0.5,0.9-0.7,1.2c-1.4,2.1-4.9,4.2-6.3,4.2c-0.2,0-0.5,0-0.7-0.1c-1.4-0.7-5.8-4.5-7.7-6.4c-1-1-2.4-1.6-3.8-1.6c-1.3,0-2.6,0.5-3.9,1.3c-0.8,0.5-1.6,0.8-2.5,0.8c-1.5,0-2.7-1-3.6-1.7c-0.2-0.2-0.4-0.3-0.6-0.4c-0.6-0.5-2.5-1.6-4.4-2.9c-2.2-1.4-4.7-2.9-5.9-3.8c-2.3-1.6-2.4-5.9-2.4-6.5c-0.1-0.4-1-2.5-1-3.7c0-0.7,0.1-2,0.2-3.3c0.1-1.4,0.2-2.7,0.2-3.3c0-1.1,0.9-2.1,1.5-2.6l0.3-0.3l0.4,0c1.3,0.1,5.6,0.3,8.3,0.3c3.2,0,4.2-0.9,5.2-1.9c0.1-0.2,0.2-0.3,0.2-0.5c0-1-1.8-2.6-4.2-4.8c-1-0.9-1.5-1.7-1.4-2.4c0.1-1,1.3-1.6,2.5-2.3c0.5-0.3,1.1-0.6,1.6-1c0.5-0.3,0.9-0.6,1.3-0.9c1.5-1,2.2-1.4,3-3.7c0.9-2.6-0.5-6.1-0.8-6.8l-0.1-0.2l0-0.3c0.1-1.1,1.1-6.6,5.7-7.5c3.5-0.7,6-2.4,8.5-4.1c1-0.7,1.9-1.3,2.9-1.9c2.3-1.3,4.8-1.6,7.8-1.6c0.7,0,1.4,0,2.1,0l0.2,0c0.7,0,1.4,0,2.1,0c4.4,0,8.8-1.5,10.3-3.4c1.1-1.4,3.3-2.3,5.8-2.3c1.3,0,2.7,0.2,4,0.7c0.8,0.3,1.6,0.4,2.6,0.4c3.7,0,7.4-2,8.1-3.8c0.4-1.1,1-3.7,1-9.9c0-0.4,0.1-1,0.3-2c0.4-2.3,1.2-6.2-0.2-7.3c-1.8-1.4-5.2-4.7-6.6-6.8l-0.7-1l1.1-0.5c1-0.5,2.6-1.2,4.2-2.2c1.7-1,1.7-2,1.5-4c-0.1-0.7-0.1-1.4-0.1-2.3c0-2.7,0.3-4.8,0.4-5.6l0.1-0.5l0.5-0.2c3.2-1.4,7.1-3.1,8.1-3.8c1.5-1,4.4-1.5,8.1-1.5c3.5,0,11.9-0.5,12-0.5l0,0c0.3-0.1,10.5-2.5,12-2.5c0.8,0,4.3-1,8.6-2.4l0.5-0.2l7.6,5.1c1.9,1.3,6.3,2.2,10.5,2.2c2.2,0,4.2-0.2,5.7-0.7c3.2-1,6.7-1.5,9.3-1.5c1.5,0,2.6,0.2,3.3,0.5c1.3,0.6,5.2,2.1,8.6,3.4l0.3,0.1c1.7,0.6,3.3,1.2,4.1,1.5c2.4,1,8.3,5,9,5.5l99.3-1.2l58.4-1l0.7,50.8l-0.3,0.4c-0.7,1-2.9,4.1-4.1,5.8c-1.6,2.3-3.2,2.7-4.6,2.7h-6.1c-0.5,0.8-3.7,5.5-5.5,6.2c-1.2,0.5-5.7,3.7-9.3,6.4l-0.2,0.1l-0.2,0c-0.4,0.1-3.9,0.9-6.4,0.9c-0.6,0-1.1,0-1.5-0.1c-0.2,0-0.3-0.1-0.5-0.1c-1.2,0-2.3,1-3.4,2c-0.7,0.7-1.5,1.4-2.4,2c-0.5,0.3-0.9,0.6-1.3,0.8l-0.2,0.1c-1.5,1-2.5,1.6-4.2,1.6h-17c-3.2,0-5.8,3.7-5.8,6.8c0,2.8-2.8,7.2-7.7,7.7c-3,0.3-4,0.7-5.4,1.2c-0.6,0.2-1.4,0.5-2.5,0.8c-0.4,0.1-0.9,0.2-1.3,0.4c-3.4,0.9-5.5,1.6-5.5,3.9c0,3.2-3.1,6.3-6.3,6.3c-1.4,0-5.2,0.1-9.2,0.2l-0.9,0c-4.6,0.1-9.3,0.3-11.4,0.3c-4,0-8.9,0-11.4,1.5c-2.3,1.4-14.7,8.9-16.3,9.9c0.4,1,1.9,5.6,1.9,7.4c0,1-0.1,6.6-0.3,12l0,0.8c-0.1,5.2-0.2,10.2-0.2,11.1c0,1.8-1.1,12.6-1.5,15.9l11.1,13.1l-7.2,8.3l-0.5-0.1c-0.5-0.1-1.5-0.2-2.7-0.2c-2.2,0-5.5,0.3-8.2,1.7c-1.5,0.8-3.5,1.1-5.8,1.1c-3.7,0-7.2-0.9-7.8-1.1l-0.1,0c-1.3-0.1-9.7-0.5-11.9-0.5c-2.4,0-7-0.9-11.7-6.6c-1.1-1.4-2.7-2.2-4.6-2.3c-0.1,0-0.3,0-0.4,0c-4.4,0-9.1,3.3-10.6,4.8c-1.9,1.9-5,8.6-6.4,11.9c0.1,0.9,1.5,9.6,2,12.9c0.5,3.5-3.4,13.4-5,16.2c-0.7,1.2-1.3,3.6-2,6.2c-0.7,2.6-1.3,5-2,6.3c-0.8,1.3-1,4.7-0.8,9.2l0.1,2.2L485.8,650z"
}, {
  id: "b14",
  parentId: "a1",
  name: "kerman",
  persianName: "کرمان",
  persianNickName: "کرمان",
  ltrRotate: 0,
  ltrX: 785,
  ltrY: 710,
  d: "M907.6,940.3c-2.3,0-5.9-2.1-8.6-3.6c0,0-0.8-0.5-1.1-0.6c-0.4-0.2-0.8-0.4-1.2-0.7c-3.5-1.9-6.2-3.6-6.9-5.3c-0.2-0.6-0.3-1.1-0.4-1.6c-0.3-1.3-0.5-2.5-2.8-4.6c-2.4-2.1-3.6-2.5-4.9-2.5c-0.8,0-1.7,0.2-2.9,0.5c-0.5,0.1-1,0.2-1.6,0.2c-3.4,0-8.1-2.1-10-3.6c-1.5-1.2-3.3-3.1-4.9-4.9c-0.8-0.8-1.5-1.6-2.2-2.3c-1.4-1.4-3.1-1.6-5.8-1.6c-0.5,0-1,0-1.5,0l-0.3,0c-0.5,0-1,0-1.5,0c-4.2,0-4.7-0.8-6.1-3.5c-1.1-2.2-2.6-4.4-6.6-6.2c-3.1-1.4-3.5-4.2-3.7-5.8c-0.1-0.4-0.1-0.8-0.2-1c-0.4-1.3-3-4-6.9-4.4c-4.3-0.4-6.1-5.1-6.1-6.5c0-0.5-0.2-2.3-0.5-4.2c-0.4-2.6-0.8-5.5-0.8-6.7l0-0.5c0-2.1,0.1-4.4-3.6-5.1c-1-0.2-1.6-0.6-1.8-1.3c-0.8-2.1,1.9-5.5,2-5.7l0,0l0,0c0.1-0.1,2.9-3,4.2-4.6c1.2-1.5,5.6-3.4,6.6-3.8c-0.3-0.9-1.2-4.3-1.2-6.1c0-1.9-1.5-2.3-2.7-2.3c-0.4,0-1.2-0.1-2.2-0.2l-0.2,0c-2.4-0.3-6.1-0.6-9.7-0.6c-5.8,0-9.9-9.7-9.9-11.6c0-1.8-2-11.3-2.5-13.6l-16.4,1.2l-1.2,4.9c-0.5,1.8-3.9,3.1-5.3,3.1c-0.6,0-2.5,0.1-4.5,0.2l-0.2-1l0.1,1c-2,0.1-3.9,0.2-4.6,0.2c-3.9,0-6.8-0.1-8.4-0.4c-2.1-0.3-5.3-3-8.6-5.8c-0.4-0.3-0.8-0.7-1.1-0.9c-2.7-2.3-4.8-6.3-5.5-8.1c-0.8-2.1-0.1-14.6,0.4-16.5c0.3-1.2,1.6-13.1,2.5-21.1l-3.9,0.4l0,0c-0.8,0.2-3.6,0.9-5.4,1.2c-1.7,0.3-5.1,2.1-7.6,3.4l-0.3,0.1c-0.5,0.3-0.9,0.5-1.3,0.7c-1.1,0.6-2.9,1.5-4.8,2.5l-0.6-0.8l0.5,0.9c-2.3,1.2-4.6,2.4-6.4,3.3c-1.6,0.8-2.9,1.2-4.2,1.2c-1.9,0-3.5-0.8-4.9-2.5c-1.6-1.8-4.4-2.1-6-2.1c-0.3,0-0.6,0-0.8,0l-0.9,0l-0.2-0.8c-0.8-3.7-1-6.2-0.6-7.4c0.7-2,2.6-14.8-0.4-19.1c-1.5-2.2-6.7-8.6-11.7-14.7l-0.3-0.3c-4.4-5.4-8.6-10.6-9.4-11.8c-1.5-2.3-3.4-5.5-3.7-6.2c-1.2-0.1-10.5-1.3-12.5-1.7c-0.2,0-0.4-0.1-0.7-0.1l-0.6-0.1l-0.2-0.6c-0.3-1.1-2.9-10.4-2.9-12c0-1.9-0.9-23.1-1.3-25.1c-0.5-2.3-1.4-3.7-2.8-4c-0.8-0.2-1.8-1.3-4.7-5.1c-1.5-1.9-3.1-4.1-4.2-5c-0.9-0.7-1.3-1.4-1.2-2.1c0.1-1.2,1.5-2.1,2.9-2.9c1.9-1.1,8.4-5.8,9.5-6.6l-0.8-33.6l0.7-0.2c1-0.4,3.2-1.2,4.1-1.5c1.3-0.4,5.5-1.7,8.9-2.1c0.2,0,0.4,0,0.6,0c3.4,0,9.5,2.6,10.3,3c3.5-1,13.7-3.9,15.4-4.6c1.7-0.7,11.8-4.6,15.6-6.1l1.5-0.6c0.1,0,6.8-2.1,11.4-3.8c4.8-1.7,16.7-8.4,17.5-12.4c0.4-2.1,1.4-3.3,2.2-4.4c0.8-1,1.6-1.9,1.6-3.6c0-3.5,5.1-5.3,7.8-5.3c2.2,0,4,1.8,4.7,2.5l3.1-1.6c2.5-1,5.4-2.5,6.3-3.3c0.9-0.9,3.4-2,6.8-3.4c0.8-0.3,1.5-0.6,2.1-0.9c2.3-1,2.4-3.6,2.4-6.2c0-0.3,0-0.5,0-0.7c0-1.6,0.4-5.3,0.8-8c0-0.2,0.1-0.4,0.1-0.5c0,0,0-0.4,0-0.9l0-0.9l0.9-0.1c4.5-0.3,7.9-0.7,8.8-1.2c0.3-0.2,0.9-0.4,2.4-0.4c2.4,0,5.8,0.5,7.8,1.2l1.1,0.4c16.3,5.4,36.1,12,37.5,13.1c0.9,0.7,7.5,3,12.7,4.8c5.7,2,8.2,2.9,8.7,3.2c0.3,0.2,1.5,0.9,2.9,1.8c7.3,4.4,14.2,8.6,15.6,10c0.4,0.4,1.5,1.5,3,2.9l0.3,0.3c9.4,9.1,18.2,17.7,19.4,19.5c1.7,2.6,7.2,8.4,12,10c4.5,1.5,6.1,4.1,6.9,5.5c0.1,0.2,0.2,0.4,0.3,0.5c0.3,0.5,0.7,1.3,1.1,2.3c0.7,1.5,1.5,3.2,2.2,4c0.5,0.5,2.3,3.1,6.3,8.7c4.8,6.9,8.5,12.1,9.2,12.7c1.2,0.8,6,5.9,6.5,6.5l0.3,0.3l0,0.5c-0.1,1.4-0.9,8.2-1.7,9.4c-0.7,1.2-1.2,11.3-1.2,15.4c0,0.8,0.7,11,1.3,21.8c0.9,14.1,1.6,25,1.6,26c0,2,1.2,12.1,2.5,15c2.4,5.6,2.9,9,1.6,10.3c-0.7,0.7-1.6,1.9-2.1,3.1c-0.4,1.1-0.4,1.9,0,2.4c1.3,1.3,2.5,9.8,2.6,10.1l0,0.1l0,0.1c-0.2,8.4,0.1,18.3,1.2,19.9c0.7,1,0.8,1.8,0.5,2.5c-0.6,1.1-2.4,1.2-3.2,1.2c-2,0-17.9-1.2-19.2-1.3c-0.6,0.4-3.2,2.2-5.8,3.3c-0.6,0.3-1.4,0.7-1.6,1.4c-0.1,0.6,0.3,1.1,0.3,1.1l4.3,5.2V820c0,2.7-2.7,3.2-7,3.2c-4.2,0-5.7,5.8-6.3,7.9l0,0.2c-0.1,0.2-0.1,0.4-0.2,0.5c-0.3,1-0.8,12.5-1.2,23.4l-3.4,30.7c-0.2,1.1-0.8,5.3-0.8,6.7c0,1,1.2,3.3,2.3,5.3c0.7,1.3,1.2,2.3,1.5,3c0.9,2.2,1.7,4.7,0.4,7.3c-1.3,2.6-1.6,3.3-1.2,4.9c0.4,1.6,3.2,5.7,6.1,6.1c3.2,0.5,3.2,6,3.2,7.8c0,1.4,0.6,7.2,0.8,8.9l0.1,1l-1,0.1c-1.4,0.2-3.2,0.3-4.3,0.3c-0.7,0-1.5,0.5-2.4,1.2c-1,0.7-2.1,1.5-3.5,1.7C908,940.3,907.8,940.3,907.6,940.3z"
}, {
  id: "b15",
  parentId: "a1",
  name: "kermanshah",
  persianName: "کرمانشاه",
  persianNickName: "کرمانشاه",
  ltrRotate: 0,
  ltrX: 165,
  ltrY: 400,
  d: "M134.1,447.8l-0.5-1.2l-0.5-1.3l-0.3-1.4l-0.3-0.9l-0.6-0.6l-0.9-0.8l-0.9-0.9l-5.1-9l-1.4,0.2l-1.9-0.1l-1.8-1l-2.1-2.8l2.4-1.1l0.5-0.3l0.3-0.3l0.8-1.6l0.4-1.8l0.8-1.8l1.6-1.3l0.9-0.9l2.3-1.9l0.3-0.4v-0.2l-0.7-1l-0.4-1.2l0.2-1.1l0.9-1.5l0.2-0.4l0.8-3.1l0.1-1.6l-0.2-1.2l-0.7-1l-0.8-0.4h-0.7l-1.5,1.1l-1.9-1.4l-0.8-1.8l-2-6.2l1.1-1.6l3.2-0.6l0.2-0.1l0.2-0.4l0.3-0.4l0.1-0.2l0.1-1.8l-0.5-2.8l0.5-3.2l3.5,0.9l2,1l1.6,0.4l4,0.3l0.8,0.2l0.1-0.7l0,0l-0.8-1l-0.3-1.5v-1.3l-0.2-1.1l-0.1-0.2l-0.2-0.2l-0.5-0.6l-0.2-0.9l-0.1-0.3l-0.2-0.3l-0.4-0.3l-0.6-0.3l-1.4-1.6l0.7-1.9l1.7-1.8l0.1-0.4l-0.2-1.4l0.3-1.2l0.9-1.2l1.1-0.5l1.6-0.2l1.1-0.7l0.2-1.1l-0.1-1.9l0.7-2.1l2.3-0.2l2,1l0.8,0.3l0.3-0.4l0.5-1.5l0.5-1.2l0.1-1l-0.5-1.7v-0.1l-0.2-0.9v-1.2l0.4-1.2l0.9-0.9l0.7-0.2l0.4,0l0-0.4v-0.6l1.2-1.9l1-0.3l1.3,0.3l1.3,0.9l0.3,0.1l0.7-0.1l1.8,0.7l0.3-0.1l0.7-0.7l1.9-1.1h1l0.8,0.2l1.3-0.4l0.7-0.1l0.1-0.1l-1.2-1.2l1.1-2.7l1.2-2l0.1-1l-1.8-1.4l2.2-0.4c0.5-0.1,3.1-0.6,5.3-1.5c0.7-0.3,1.2-0.4,1.8-0.4c0.4,0,0.8,0.1,1.2,0.3c1,0.5,1.7,1.5,2.3,3.3c0.4,1.3,1.9,2.4,3.2,3.4c1.7,1.3,3.3,2.5,3.3,4.2c0,1.9,0.2,8.2,3.4,10.3c1.3,0.9,3.1,1.4,4.7,1.8c2,0.6,3.8,1.1,4.4,2.3c0.9,1.7,2.5,4.6,2.9,5.4c1.2,0,9.1,0,11.9,0.5c0.1,0,2.3,0.4,4.6,0.4c3.2,0,4.2-0.7,4.5-1c0.2-0.3,0.3-0.6,0.1-1c-0.2-0.5-0.4-1.1-0.6-1.6c-1-2.6-2-5.3,0.2-6.7c1.7-1,3.4-2.5,4.3-3.3l0.7-0.6l0.7,0.7c0.3,0.3,1.1,0.8,3,0.8c1.6,0,5.3-0.4,5.3-3.8c0-2.8,1.1-5.8,3.3-5.8h14c3.3,0,9.7,0.9,10.2,3.2c0.2,0.7,0.2,1.5,0.2,2.3c0,1.8,0.1,3,1.2,3.6c1.3,0.6,2,1,2.1,1.8c0.1,0.7-0.4,1.5-1.5,2.6c-2.3,2.3-3.5,6.2-2.5,8.2c0.4,0.8,0.6,2.2,0.7,3.7c0.3,2.2,0.5,4.6,1.6,5.2c2.1,1,3.6,1.5,6.4,2c2.4,0.4,4.8,1.4,5.7,1.8l0.5,0.2l0.1,0.6c0.1,1.4,0.5,4.9,0.5,6.1c0,1.6-3.7,5.3-4.1,5.7l-3.9,4.4c0,0-0.5,0.6-1,1.3l-0.3,0.5h-7l-1.5-0.9l-1.6,0.4l-3.3-2c-0.5,1.6-1.2,3.9-1.3,4.5c-0.1,0.8-1.1,5-2.5,6c-0.5,0.4-1.3,1.3-2.1,2.2c-1.2,1.4-2,2.4-2.7,2.8c-0.9,0.6-2.7,2.6-3.5,3.6v2.1l0,0.1c0.6,1.9,0.9,2.3,0.9,2.3c0.4,0.4,1.5,1.6,1.8,2c0.2,0.3,0.9,1.5,1.3,2.4l1.1,2l-2.2-0.6c-2.6-0.7-7.2-2.1-8.7-2.8c-0.2-0.1-0.4-0.2-0.6-0.2c-0.1,0-0.3,0-0.3,0.1c-0.5,0.5-0.1,2.1,0.3,2.7c0.7,1.1,1,3.5,1,5.5c0,2.2-3.1,4.6-5.9,4.6c-2.7,0-8.6-2-11.4-3c-0.7-0.2-1.3-0.4-1.8-0.4c-0.4,0-0.8,0.1-1.1,0.3c-0.4,0.2-0.9,0.7-1.1,1.9c-0.1,0.5-0.4,0.9-1,1.3c-1.6,1-4.4,1.4-6.3,1.4c-0.8,0-1.5-0.1-2-0.2c-0.7-0.2-1.8-0.3-2.9-0.4c-2.4-0.2-5.4-0.4-6.9-2c-1.1-1.3-4.6-4.2-7.6-6.7c-2.4-2-4.7-3.9-5.7-4.9c-1.2-1.2-2.7-1.8-4.5-1.8c-1.3,0-2.5,0.3-2.9,0.5c-0.3,0.1-0.6,0.1-1,0.1c-2.3,0-6.2-1.9-8.6-4.9c-0.9-1.1-1.4-1.3-1.6-1.3c-0.5,0.1-0.7,1-0.9,1.8c-0.1,0.4-0.2,0.8-0.4,1.2c-0.7,1.8-2.7,2.9-5.2,2.9c-0.3,0-0.7,0-1-0.1c-0.9-0.1-1.6-0.1-2.2-0.1c-1,0-1.5,0.2-1.9,0.5c-0.3,0.2-0.6,0.7-0.6,2.1c0,2,1,3,2,4c0.5,0.5,0.9,1,1.3,1.5c0.2,0.4,0.4,1,0.1,1.8c-0.5,1.4-2,2.7-3.3,3.2c-0.8,0.3-1.5,1.3-2.3,2.3c-0.7,1-1.6,2.2-2.9,3.3c-2.5,2.1-7.4,4.6-8.3,5l-0.1,0.4l-0.5,0.2c-0.1,0-0.3,0.1-0.4,0.1l-0.6,0.1L134.1,447.8z"
}, {
  id: "b16",
  parentId: "a1",
  name: "khorasanshomali",
  persianName: "خراسان شمالی",
  persianNickName: "خراسان شمالی",
  ltrRotate: 0,
  ltrX: 760,
  ltrY: 190,
  d: "M856.5,250.1c-3.1,0-7.2-1.5-8.7-4.1c-0.8-1.3-3.6-2.1-6.3-2.8c-2.2-0.6-4.5-1.2-5.6-2.1c-0.6-0.5-1.2-1-1.8-1.6l-0.1-0.1c-2-1.9-4.5-4.3-7.5-4.3c-2.6,0-6.7-1.1-10.6-2.1c-2.2-0.6-4.2-1.1-5.9-1.4c-4.5-0.9-8.3-3-9-3.5c-1.7,0.8-11.9,5.7-17.4,7.9c-5.6,2.3-8,7.2-8.3,7.8l-0.1,0.8l-0.9,0c-0.5,0-1.1-0.1-1.7-0.1c-4.5-0.5-7.9-3.8-8.5-4.4l-0.2-0.2l-0.1-0.2c-0.2-0.7-1.2-4-2.9-5.7c-1.8-1.9-3.7-5.8-4-6.5l0-0.1l-0.9-3.2c-4,1.7-8.7,3.8-9.7,4.8c-0.9,0.9-2.2,1.5-3.1,1.5c-0.3,0-0.5,0-0.7-0.1c-0.5-0.2-1.1-0.7-1.1-2.1c0-0.5,0-1,0-1.5c-0.1-2.8-0.2-6,1.6-8.1c1.7-2.1,2.4-4.4,2.4-7.3c0-2.9-0.6-5.8-1.8-5.8h-4.7l-0.5-9.5h4.5c0-1.6,0.2-10.1,2.6-12.4c2.4-2.4,8.4-10.2,8.9-10.9l1-8.5l6-5v-7.8l-1.5-7.4l-1.3-0.2l0.7-1.3l0.1-1l-0.1-0.7l-1.8-1.9l0.6-1.8l4-3.3l2.1-1.4l2.4-0.9l5.7-0.1l1.2,0.2l1,0.5l0.8,0.6l0.4,0.2l0.6-0.1l4.7-1.9l3.1-0.6l0.9,0.2l2.4,1.8l1.9,1l0.7,0.2l8.8,1.5l2.4,0.9l0.7,0.1l0.6-0.4l0.8-0.6l1.9-1.2l0.5-0.5l1.2-1.9l0.9-0.9l1.4-0.7h1.7l1.6,0.5l1,0.7l0.4,1v0.5l0.1,0.3l1.4,2.1l1,2.4l0.6,0.8l2,2l0.7,2.2l1.3,1.6l0.4,1.6l-0.2,1.5l-1,3.2l0.9,1.3l8,2.9l0.6-0.1l0.9-0.3l1.2-0.1l1.2,0.1l2.9,0.8l2.6-0.1l0.9-0.2h1.3l1.1,0.7l0.7,0.6l0.5,0.3l0.1,0l1-0.2l1,0.2l0.7,0.7l0.5,1l0.2,0.2l0.4,0.2l0.7-0.1l0.9-0.2l1.2-0.1l2.4,0.6l9.2,4.2l3.6,0.8l2,0.2l1,0.2l1.3,0.5l0.9,0.9v1.1l-0.2,0.4l0,0.1l0.9,1.5l0.3,0.7l0.2,1.5v0.8l0.1,0.4l0.7,0.5l0.7,0.3l4.6,0.6l0,18.1c0,0.6-0.5,9.1-0.5,11c0,2.2-3.4,4.4-6.6,6.2c-1.1,0.6-1.6,1.5-1.6,2.6c-0.1,1.9,1.4,3.9,2.2,4.5c0.5,0.3,1.2,0.6,1.9,0.9c1.4,0.6,2.8,1.1,3.2,2.2c0.5,1.4-0.3,3.9-0.4,4.4l-0.1,0.3l-0.2,0.2c-0.8,0.6-3.6,2.7-7.9,4.4c-4.8,1.9-3.9,7.1-3.9,7.1l0,0.1l0,0.1c0.1,2,0.7,8.3,2,10.4c0.4,0.6,0.2,1.2,0,1.5C864.1,249.2,858.5,250.1,856.5,250.1z"
}, {
  id: "b17",
  parentId: "a1",
  name: "khorasanrazavi",
  persianName: "خراسان رضوی",
  persianNickName: "خراسان رضوی",
  ltrRotate: 0,
  ltrX: 875,
  ltrY: 320,
  d: "M983.8,429.8c-0.7,0-1.3-0.1-2-0.4c-2.1-0.9-2.3-3.9-2.5-5.8c-0.1-0.6-0.1-1.1-0.2-1.3c-0.3-1-3.9-3.1-6.7-3.5c-2.7-0.3-17.8-0.4-19.5-0.4l-0.6,0l-0.3-0.5c-0.7-1.2-2.5-4.1-4.8-6.1c-1.6-1.4-2.1-1.6-2.7-1.6c-0.2,0-0.4,0-0.7,0.1c-0.4,0.1-1,0.2-1.8,0.2c-1.5,0-7,0.2-11.9,0.4c-5.3,0.2-9.5,0.3-10.7,0.3c-1,0-3.2,0.1-5.8,0.3c-3.8,0.2-8.4,0.5-11.7,0.5c-3.8,0-5,2.6-5.4,3.8l-0.4,1.4l-1.2-1c-3.5-2.9-7.8-6.5-8.9-7.6c-1.5-1.5-5.9-7.7-7-10.6c-0.2-0.5-0.5-0.9-1-1.1c-0.3-0.1-0.6-0.2-1-0.2c-1.5,0-3.1,0.8-3.4,1c-0.3,0.5-2.1,3.4-6.4,3.4c-0.2,0-0.5,0-0.7,0c-5.1-0.4-5.9-0.7-7.8-3.4c-1.1-1.6-6.9-3.1-12.1-3.8l-0.6-0.1l-0.2-0.6c-0.2-0.7-0.9-2.6-2-4.2l-0.8-1.2c-1.9-2.9-6.4-9.7-8.3-11.9c-2.2-2.5,0.7-6,2.2-7.9l0.3-0.4c0.9-1.1,3.1-2.2,6-3.5c1.4-0.6,2.6-1.2,3.1-1.6c0.2-0.2,0.3-0.4,0.4-0.7c0.1-1.3-1.4-3.5-2.9-5.1c-1.7-1.7-5.3-4.3-7.6-5.4c-0.6-0.3-1.3-0.6-2.1-0.8c-1.9-0.7-3.9-1.4-5.3-3.3c-0.4-0.6-1.9-1.5-7.5-1.5c-3.1,0-6.7,0.3-9.1,0.5l-0.3,0c-2.9,0.3-8.3,3-11.8,4.9c-1.3,0.7-2.2,1.1-2.6,1.3c-1.6,0.7-5.3,4.6-5.7,6.4c-0.4,2-6.8,7.9-9.2,9.6c-1.9,1.4-5.8,4.2-11.1,4.2c-0.6,0-1.2,0-1.8-0.1c-4.2-0.5-9.1-0.7-11.7-0.7l-2,0l1.9-2.4c2.4-3,5-6.3,6.2-7.5c2.4-2.4,4.8-7.1,5-7.6c1.7-3.4,5-5.3,9.7-5.6c5.9-0.3,8.8-5,9.8-6.5l0.2-0.3c0.7-1.1,3.6-2.7,7.5-2.7c2.6,0,7-0.7,7-3.4c0-0.7-0.2-1.9-0.5-3.2c-0.6-3.2-1.4-7.6,0.1-10c2.1-3.1,0-7.7-1.8-9.9c-1.3-1.5-9.5-8.7-16.1-14.3l-0.3-0.3l-0.4-10l5.2-13l-7.6-10.1l9.1-7.1c0-2.8-0.2-6.3-0.5-7.3c-0.2-0.6-1-1.3-1.9-1.9c-1.3-1-2.1-1.8-2.1-2.6c0-0.2,0-0.5,0-0.8c0-1.1,0.1-2.5-0.5-3.1c-0.2-0.2-0.5-0.3-0.8-0.3c-0.9,0-1.1,0.2-1.4,0.6c-0.5,0.5-1,1-2.5,1.4l-0.6,0.2c-1.8,0.6-3,1-5.1,1l-1.7,0l0.8-1.5c0.7-1.3,3.3-5.6,8.4-7.7c5.3-2.2,15.2-6.9,17.1-7.8l0.5-0.2l0.5,0.3c1,0.6,4.4,2.4,8.6,3.3c1.7,0.3,3.7,0.9,5.8,1.4c4,1,8,2.1,10.6,2.1c3.2,0,5.6,2.3,7.8,4.4c0.7,0.6,1.3,1.2,1.8,1.7c1.1,0.9,3.2,1.4,5.4,2c3.5,0.9,5.8,1.7,6.6,3c1.5,2.4,5.4,3.9,8.3,3.9c2.4,0,7.4-1,8.3-2.6c0.2-0.3,0.2-0.7,0-1c-1.5-2.5-2-10.4-2-10.7c-0.3-2,0.1-6.1,4.2-7.7c4.6-1.8,7.4-4.1,7.9-4.4c0.3-1,0.8-3.2,0.5-4.3c-0.3-0.9-1.6-1.4-2.9-1.9c-0.8-0.3-1.5-0.6-2-1c-1-0.7-2.5-2.9-2.4-4.9c0-1.3,0.7-2.3,1.9-3c3.3-1.9,6.4-3.9,6.4-5.8c0-1.7,0.4-9.8,0.5-11v-18.8l2.9,2.1l0.4,0.1l4.9-0.5l0.6-0.3l0.6-0.8l0.6-1.2l0.8-1.2l1.3-0.8l1.6-0.1l1.4,0.7l2.9,2.5l2.2,0.8l1.2,0.2l1-0.1l0.2-0.1l0.4-0.4l0.7-0.5h1l1.2,0.2l0.4-0.1l0.3-0.1l0.4-0.5l0.1-0.9l0.9-1.5l4.3,2.3l4.5,0.9l2.5,1.1l0.7,0.5l0.6,0.2l1.7,0.3l1,0.4l2,2l7.5,5l0.7,0.1l3.4-1.5l2,0.6l1.3,1.2l1.4,1.7l0.3,1.3l-0.1,1.4l0.2,0.6l0.3,1l-0.5,1l-0.3,0.6l-0.1,0.5l0.1,1.2l1.1,4.4l0.5,0.7l3.5,2.8l1.2,1.2l0.8,1l-0.3,1l-0.2,0.2l-0.1,0.4l0.5,0.1l0.6,0.6l0.3,0.2l0.2,0.1h0l2-0.7l1.4,0.2l1.4,1.4l0.5,1.4l0.3,1.4l0.3,0.8l0.1,0.1l0.1-0.1l0.8-1.1l1-0.6l1,0.2l8.7,2.7l3.9,3.1l1.9,1.1l4.8,0.8l2.4,1l2,2.5l2.2,4.4l2.6,3.9l6.2,7.1l1.3,2l1.7,4.2l1,1.7l1.5,0.8l42.7-0.8l3,0.5l3.1,0.4l0.5,3l0.4,0.9l0.4,0.9v2.1l-0.4,1l-0.6,1.2l-0.2,0.4l0.1,0.5l0.3,1.3l-1.3,5.7l-0.3,3l1,2.3l-0.3,0.4l0.4,0.2l0.8,1.1l0.3,1l0.1,0.8v1.5l0.1,0.4l0.9,1.3l1,4.6l0.1,2l0.1,0.4l-0.2,1l-0.7,0.8l-0.2,0.3l-0.1,0.4l-0.1,0.5v0.7l-0.3,1.3l-0.9,0.6l-0.5,0.2l0,0.3l0.2,1.4l-0.2,1l-1,1.1l-0.7,0.5l0.7,0.1l1.5,0.7l1.2,1l0.9,1.2l0.8,1.1l0.6,1.3l0.3,1.3l0.3,2.6l0.2,1l0.1,1.4l-0.3,1.2l0.3,0.4v1.2l-0.5,2l0.1,1.3l-0.4,0.9l-0.8,0.8l0,0l0.1,1.3l0.7,1.4l1.4,2l0.6,0.8l0.7,3.1l0.1,1.6l-0.4,1.7l-0.9,1.5l-1.4,1.5l-0.5,1.2l-0.5,2.2l-0.5,0.9l-1.2,1.5l-0.2,0.6l-0.3,1.2l0.3,3.7l-0.7,1.8l-1.5,0.8l-1.6,0.4h-1l-0.3,0.2l-0.2,1l-0.1,1.3l0,0.3l0.2,0.2l0.5,1l-0.2,1.5l-0.5,0.3l2,2.6l0.2,0.7l-0.1,1l-0.1,0.5l0,0.1l1,1l-1.9,2.5l-0.4,0.8l-0.3,2.8l-0.9,2.6l-0.1,1.3l-0.3,1l-0.9,1.2l-0.1,0.5v0.5l0.3,1.3v0.7l-0.2,2.7l-0.6,2.8l-1.8,0.6l-0.2,0.8l-1.4,2.3l-1.9,1.5l-0.8,0.9l-0.1,1.2l0.2,1.8l-0.2,2.1l-1,1.3l-1.2,0.2h-0.8l-0.6,0.1l-0.4,0.2l-0.5,0.8l-2.8,3.1l-1.3,1l-1.7,0.5l-3.1,0.4l-1.1,0.5l0,0.1l0.3,0.2l0.6,0.8l0.5,1.5l0.2,0.2l1.3,0.7l1,0.8l0.6,1l0.9,1.8l4.4,5.5l1.5,2.8l-14.8,0.8l0.2,0.8l-1.4,1.5l-2.8,1.4l-1.9,2l-1.8,2.2l-1.5,3l-0.4,2.8l0.2,2.2l-1.7-1.2h-10.1c-0.9,0-3.4,3.1-4.9,5.7C987.1,428.7,985.6,429.8,983.8,429.8z"
}, {
  id: "b18",
  parentId: "a1",
  name: "khorasanjunubi",
  persianName: "خراسان جنوبی",
  persianNickName: "خراسان جنوبی",
  ltrRotate: 0,
  ltrX: 815,
  ltrY: 480,
  d: "M943.3,661.7c-3.2-3.4-5.6-5.8-6.3-6.3c-0.8-0.6-3.6-4.6-9.4-12.8c-2.8-4-5.7-8.1-6.2-8.6c-0.8-0.8-1.6-2.5-2.3-4.1c-0.4-0.8-0.8-1.8-1.1-2.3c-0.1-0.1-0.2-0.3-0.3-0.5c-0.9-1.4-2.3-3.8-6.7-5.3c-5-1.7-10.5-7.4-12.3-10.2c-1.3-1.9-13.4-13.6-19.1-19.2l-0.2-0.2c-1.6-1.6-2.9-2.8-3.3-3.2c-1.6-1.6-10.6-7-15.5-9.9c-1.5-0.9-2.6-1.6-2.9-1.8c-0.5-0.3-4.4-1.7-8.6-3.1c-8-2.8-12-4.2-12.8-4.8c-0.7-0.5-6.4-2.8-37.4-13l-1.1-0.4c-1.4-0.5-5-1.2-7.6-1.2c-1.4,0-2,0.2-2.3,0.3c-1.4,0.7-7.2,1.1-8.9,1.2l-1.1,0.1l0-1.1c0-1.9,0.1-4.5,0.4-5.9c0.3-2.1,1.6-3.4,2-3.8c-0.9-1.5-6.6-11.5-10.3-14.5c-3.1-2.6-8.3-11.3-11-16c-0.8-1.4-1.4-2.5-1.8-2.9c-1.3-2-6.8-7.2-9.6-7.5c-2.6-0.3-13.6-3.4-16.9-4.3l-0.4-0.1l-0.2-0.3c-0.8-1.2-7.9-11.9-8.2-14.1c-0.3-1.7-2.8-6.8-4-9l-11.2-16.1l0.6-0.6c0.3-0.4,0.6-0.7,0.8-1c1.3-2,3.9-5.6,4.3-6.1l-0.7-50.6l26.3-0.5c1.2-2.2,14.2-26.1,15.6-27.6c0.5-0.5,1.6-1.8,2.5-3l0.3-0.4l0.5,0c1.2,0,7.7,0.1,12.9,0.7c0.6,0.1,1.2,0.1,1.8,0.1c5,0,8.8-2.6,10.7-4.1c2.6-1.9,8.6-7.6,9-9.3c0.4-1.9,4-5.9,6-6.7c0.5-0.2,1.4-0.7,2.6-1.3c3.6-1.9,9-4.6,12-4.9l0.3,0c3.7-0.3,6.9-0.5,9.3-0.5c5.7,0,7.1,0.9,7.7,1.7c1.2,1.7,3.2,2.4,5,3.1c0.8,0.3,1.5,0.5,2.2,0.9c2.1,1,5.8,3.6,7.7,5.5c1.6,1.6,3.2,3.9,3.1,5.5c0,0.5-0.2,0.8-0.6,1.1c-0.6,0.4-1.8,1-3.2,1.6c-2.3,1-5,2.3-5.9,3.4l-0.3,0.4c-2,2.5-4,5.2-2.2,7.3c1.9,2.2,6.4,9,8.3,11.9l0.8,1.2c1.2,1.9,2,4,2.2,4.6c1.4,0.2,11,1.6,12.7,4.1c1.7,2.4,2.4,2.8,7.5,3.2c0.2,0,0.5,0,0.7,0c3.8,0,5.4-2.3,5.9-3l0.2-0.2l0.3-0.1c0.5-0.2,2-1,3.5-1c0.4,0,0.8,0.1,1.1,0.2c0.6,0.2,1.1,0.7,1.3,1.4c1.1,2.8,5.4,9,6.9,10.5c1.3,1.3,7.7,6.6,9.4,8.1c0.3-1.9,1.8-4.9,6-4.9c3.2,0,7.9-0.3,11.7-0.5c2.6-0.1,4.8-0.3,5.8-0.3c1.3,0,6.2-0.2,10.6-0.3l0.1,0c5.1-0.2,10.3-0.4,11.8-0.4c0.8,0,1.3-0.1,1.8-0.1c0.3,0,0.6-0.1,0.8-0.1c1,0,1.7,0.6,3.1,1.7c2.6,2.3,4.7,5.7,5.1,6.5c1.8,0,17.1,0,19.9,0.4c2.9,0.4,6.7,2.6,7.1,3.8c0.1,0.3,0.1,0.7,0.2,1.4c0.2,1.7,0.4,4.6,2.2,5.4c0.6,0.3,1.2,0.4,1.8,0.4c2,0,3.3-1.5,4-2.8c1.3-2.3,3.9-5.7,5.1-5.9l0.1,0h10.2l1.4-1.3l0.9,7.5l1.6,10.7l-0.1,3l-1.8,4.1l-0.4,1.9l1.3,4.5l3.4,3.2l4.4,1.8l4.4,0.4l4.3-0.3l2.5,0.2l2.1,0.6l1.1,0.6l1.2,1.1l0.8,1.6l-0.9,1.7l-1.3,0.5l-2.7,0.2l-0.4,0.2l0,0.3l0.2,1.1l0.1,1.4l-0.4,1.7l-0.8,1.1l-2.1,1.3l-1.6,1.4l-10.9,14.7l-0.2,0.6l0.1,5.2l0.8,4.3l10.3,34.4l4.5,17.2l-0.1,5.8l-0.8,5.6l-0.4,1.5l-1.6,1.9l-0.1,0.4l0.2,0.1l0.7,1l-0.6,1.8l0,0.3l0.6,1.4l0.1,1.8l-0.5,4.3l0.2,3.3l0.8,6.4l-0.8,5.2l0.2,1.4l0.8,3.3l0.6,6l1.3,0.5l1.3,0.2l-0.6,1.3c-0.7,1.3-4.4,8.1-6.3,10.1c-2.3,2.3-6.1,3.8-8.1,3.8c-1.1,0-5.1,1.1-9.2,2.4c-3,0.9-6.4,1.9-8.3,2.3c-0.9,0.2-1.5,0.6-2,1.4c-1.3,2.1-0.8,6.3,0.1,9.2c1,3.4-3.8,6.6-4.3,7c-1.4,0.9-7.8,1.7-11.9,1.7c-1.4,0-2.3,0.3-2.9,0.8c-0.7,0.7-0.7,1.7-0.6,2.7l0,0.4c0,1.3-0.5,5.3-0.8,7.6l-0.1,0.6l-28,11.4L943.3,661.7z"
}, {
  id: "b19",
  parentId: "a1",
  name: "khuzestan",
  persianName: "خوزستان",
  persianNickName: "خوزستان",
  ltrRotate: 0,
  ltrX: 295,
  ltrY: 610,
  d: "M304.3,706.3h-0.5v0l-0.1,0l-0.1,0.1l-2.5-0.8l-1.8-1.3l-0.5-0.5l-0.4-0.7l-0.6-1.5l-0.1-0.9l-0.9-3l-0.1-0.1l-0.4-0.9l-1.2-1.3l-0.8-1.9l-0.2-0.8l0.2-1.3l0.7-0.8l0.6-0.6l0.3-0.3l0-0.3l-0.1-0.5l-0.2-0.4l-0.3-0.4l-2.2-2.2l-2-2.3l-1.2-1.9l-0.3-0.3l-0.4-0.1h-0.5l-2.2,0.3h-0.8l-0.8-0.1l-1-0.4l-0.8-0.8l-0.3-0.9l-0.5-3.1l-0.4-1.3l-0.7-1.1l-0.9-0.9l-0.4-0.3l-0.4-0.1l-6.9-1l-0.1-2.9l0.2-33.2l-0.1-0.4l0,0h-20l0.4-29.7l9-24.7l0.3-1.2l-0.1-1.1l-0.6-0.9l-2.2-1.7l-1.2-1.2l-0.3-0.8l-0.3-1.2l-0.2-0.4l-0.2-0.2l-1.2-0.8l-0.5-0.8l-2.5-4.4l2.5,1.1c0.3-1.3,1.4-6.2,2.8-7.3c0.5-0.4,1.2-0.9,1.8-1.4c1.4-1,3-2.1,3.6-3.1c1-1.5,3-5.8,3.5-7.4c0.4-1.5,1.9-6.2,2.3-7.7l0.1-0.5l1.3-3.5l0-6.6l-0.2-2.2l-0.8-1.3l-1.1-1.4l1.1-1.8l0.7,0c0.6,0,1.1-0.1,1.3-0.4c0.4-0.5,0.5-1.4,0.2-1.7l-0.2-0.2l-0.1-0.2c-0.1-0.6,0.3-1.4,0.9-1.7l0.1,0c0.3-0.1,2-0.8,4.1-1.8c0.2-0.4,1-1.9,1.3-2.2l0.1-0.1l0.1-0.1c0.2-0.1,0.1-0.9-0.2-1.4c-0.1-0.1-0.2-0.3-0.3-0.5c-0.4-0.7-0.5-0.9-0.6-1.2l0-0.1v-0.1c0-0.1-0.1-0.6-0.5-1.4l-1-2l-1.6-2.4l0.6-0.6c1-0.9,3.6-3.3,5.1-5.4c1.8-2.3,6.2-3.2,9.6-3.2c0.6,0,1.1,0,1.7,0.1c1.5,0.2,4.4,0.3,7.5,0.3c3.1,0,5.7-0.1,6.8-0.2c0.5-0.1,1.1-0.1,1.5-0.1c2.1,0,3.9,0.7,5.7,2.2c2.1,1.8,9.2,2.3,11.5,2.3c1.8,0,5.5,1,8.1,2c2.6,1,6.2,1,7.9,1c0.2,0,0.5,0,0.8,0l0.1,0c0.4,0,0.9,0,1.4,0c2.9,0,4.7,0.3,5.8,1.1c2.2,1.4,3.4,2.8,4.4,4.8l0.3,0.5c1.3,2.5,4.6,9.3,7,11.1c1.6,1.2,4.5,3.8,6.8,5.9c1.3,1.2,2.8,2.5,3.5,3.1c0.8,0.7,2.7,2.6,4.7,4.6c1.9,1.9,4.1,4.1,5.3,5.1c2,1.7,1.7,3.1,1.3,4.4c-0.1,0.3-0.2,0.6-0.2,0.8c-0.3,1.6,1.6,6.8,3.3,8.8c1.7,2,7.3,8,9.3,9.3c1.7,1.2,7.1,6,8.7,7.4l0.4,0.4l-0.1,0.5c-0.8,4.7-0.6,7.5,0,8c1.4,1.4,3.7,3.7,5,4.6c1.1,0.8,2.3,2.8,2.8,3.6l0.4,0.6l-0.4,0.5c-5.1,6.2-7.5,9.7-7.6,10.5c0,0.2-0.1,0.5-0.1,0.8c-1,5.7-2,8.5-3.3,9.4c-1.7,1.1-2.8,2.3-3.6,3.9c-0.4,0.7-1.5,1.5-6.9,1.5c-0.5,0-1.2,0-1.9-0.1c-1,0-1.9-0.1-2.5-0.1c-0.7,0-1.3,0-1.5,0.1c-0.4,0.1-0.7,0.9-0.7,1.8c0,1.1,0.6,1.8,1.7,2.1c2.7,0.7,3.3,3.3,2.8,5c-0.1,0.3-0.1,0.8-0.1,1.3c-0.1,1.8-0.2,4.5-2.3,6.1c-1.4,1-2.8,2.3-3,3.5c-0.1,0.6,0.1,1.2,0.7,1.8c1.7,2,3,4,4,6c0.7,1.4,2.5,2.2,5.1,2.2l0.6,0c0.7,0,0.7,0,1.7-2l0.4-0.8c1.1-2.2,2.4-2.9,3.3-3c0.1,0,0.3,0,0.4,0c0.6,0,1.2,0.2,1.7,0.7c1.1,1.1,1.4,3.8,1.1,4.9c-0.2,0.5-0.4,2.6,0.5,4.1c0.5,0.9,1.3,1.4,2.4,1.6c0.7,0.1,1.4,0.2,1.9,0.3c2.1,0.3,3,0.5,3.6,2.2c0.8,2.5,1.9,3.9,3.1,4.2c1.1,0.2,2.7,2,2.9,3.6c0.1,1.1-0.4,2-1.5,2.5c-2.9,1.3-4.2,1.9-4.2,3.4c0,1.6,1.3,4.2,4.2,6.1c2.1,1.4,3.1,3.6,3.1,6.5c0,1,0.3,10.9,0.3,11.3l0.1,1.9l-6.1-2.3l-0.1,0c-0.4-0.2-2.5-1.2-4.7-3c-1-0.9-2-1.6-2.8-2.3l-0.1-0.1c-1.1-0.9-2-1.6-2.8-2.3c-0.1-0.1-0.2-0.2-0.3-0.2c0,0-0.1,0-0.1,0c-0.8,0.3-1.8,3.2-2.1,5.7c-0.3,2-1.8,3-3.1,3.2l-1.1,0.5l-0.3-1.1l0-0.2l-0.2-0.4l-0.6-0.4l-1.8-0.7l-1.8-0.3l-2,0.4l-1.9,0.6L367,701.6l-2.5,1.1l-2.6-0.5l-1.9-3l-0.3-1.4v-3.1l-0.4-0.9l-0.4-0.6l-0.1-0.2l-0.1-0.1l-0.5-0.3l-0.4-0.2l-0.3-0.1l-1.1-0.1l-0.5,0.1l-1.2,0.3l-1,0.1l-1-0.3l-0.9-0.6l-0.1-0.1l-0.8,0.1l-2.2,1l-1.4,0.2l-2-0.1l-1.2-1.2l0.1-2.8l-0.8-0.5l-0.4-0.8v-0.2l-0.7,0.7l-1.7,0.3l-1.7-1.1l-0.6-1l-0.3-0.3l-0.7-0.1l-1.6-0.6l-4-2.4l-1.1-1l-0.4-2.4l-0.8-1l-1.2-0.6l-2.7-0.7l-0.4,0.4l-0.1,0.2l-0.4,0.7l-0.1,0.2l0.8,0.7l-0.8,1.3l-0.3,0.4l0.3,0.9l0.8,0.8l1.2,1l1.1,1.2l0.6,1.5l0.4,1.6l0.3,3.3l-0.1,1.1l-0.5,1.5l-0.1,0.5l0.1,0.5l0.3,1.4v0.9l-0.4,1.7l-1,1.5l-1.4,1.1l-1.6,0.4l-3.8-0.4l-1.3,0.5l-1.3-0.6h-4.1l-2.2-1.2l0.1,0.2l0.9,1.4l0.1,1.3l-0.2,1.1l-0.7,0.9l-1.2,1l-1.7,0.5L304.3,706.3z M341,675.6l1.3,0.5l0.8,0.7l0.8-1.6l1.7-2.2l0.1-0.2l-0.2,0l-1.4-1l-0.7-1.4l-0.2-1.1l-0.2,0.3l-2.8,2.2l0.3-2.9l-1.3,0.3l-0.9-0.7l-0.5-0.7l-0.4,0.3h-0.7l-1.3-0.2l-0.9-0.3h-0.6l-1.1,0.5l-2-0.3l-1.1,0.7l-0.1,0.2l0.7,0.3l1.9,0.4l2,1.2l0.7,2.2l-0.4,0.5l0.8-0.2l1.5,0.4l2.5,1.3l0.6,0.2L341,675.6z"
}, {
  id: "b20",
  parentId: "a1",
  name: "kvab",
  persianName: "کهکیلویه و بویراحمد",
  persianNickName: "ک و ب",
  ltrRotate: 50,
  ltrX: 750,
  ltrY: 90,
  d: "M426.1,709.9c-0.1-0.1-0.2-0.1-0.3-0.2l0,0c-0.4-0.1-3.1-1.1-4-2c-0.6-0.6-0.9-1.5-1.3-2.7c-0.4-1.1-0.9-2.5-1.7-4c-1.7-3-2-10.1-2-10.4c0-0.1-0.3-10.3-0.3-11.4c0-2.8-0.9-4.8-2.9-6.1c-3.1-2-4.4-4.8-4.4-6.5c0-1.8,1.5-2.5,4.5-3.9c0.6-0.3,1.3-0.8,1.2-2c-0.2-1.4-1.5-3-2.5-3.2c-1.5-0.3-2.6-1.8-3.5-4.5c-0.5-1.4-1-1.5-3.2-1.9c-0.6-0.1-1.2-0.2-1.9-0.3c-1.2-0.2-2.1-0.8-2.7-1.8c-1-1.6-0.7-3.8-0.5-4.5c0.3-0.9,0-3.5-0.9-4.4c-0.3-0.3-0.8-0.5-1.3-0.5c-0.1,0-0.2,0-0.3,0c-0.6,0.1-1.9,0.6-2.9,2.8l-0.4,0.8c-0.8,1.5-1,1.9-1.3,2.2l-0.1,0l-0.1,0c-0.2,0.1-0.4,0.1-0.7,0.1l-0.7,0c-2.8,0-4.7-0.9-5.5-2.5c-1-2-2.3-4-4-6c-0.6-0.7-0.9-1.5-0.8-2.2c0.2-1.4,1.7-2.7,3.2-3.8c1.9-1.4,2-3.9,2.1-5.7c0-0.7,0.1-1.1,0.1-1.4c0.2-0.8,0.1-1.8-0.2-2.6c-0.4-0.9-1.2-1.5-2.2-1.8c-1.1-0.3-1.9-1.1-2-2.2c-0.2-1,0.2-2.1,0.8-2.5l0.1-0.1l0.1,0c0.3-0.1,0.8-0.2,1.7-0.2c0.8,0,1.7,0,2.4,0.1l0.2,0c0.7,0,1.3,0.1,1.8,0.1c1.4,0,5.8,0,6.4-1.2c0.6-1.1,1.5-2.6,3.8-4.1c1.6-1.1,2.6-6.5,3-8.7l0.3-1.5l1.3,0.8c2.7,1.7,4.5,2.9,5.4,3.4c0.5,0.3,1,0.4,1.6,0.4c1.2,0,2.6-0.7,3.9-1.4c1.7-1,4.3-2.1,6.4-2.1c0.7,0,1.3,0.1,1.8,0.4l0.4,0.2c1.5,0.7,1.6,0.9,3.2,3.2l0.5,0.7c2.3,3.3,4.6,4.9,7.1,4.9c0.7,0,1.3-0.1,1.8-0.3c0.5-0.1,0.9-0.2,1.4-0.2c1.6,0,2.3,1.2,3,2.9c1.6,4.1,3.4,7.9,5.8,7.9c0.2,0,0.4,0,0.6-0.1c2-0.4,3-1.8,4-2.9c0.4-0.5,0.8-1,1.3-1.4c1.1-0.8,2.7-1.2,3.3-1.3l0.2,0l5.8,1l0.1,0.7c0.5,3.6,0.7,5.8,0.7,6.8c0,4.8,1.5,8.6,4.2,11.2c3,2.7,17.8,14.2,20.8,16.5l0.3,0.2l1.2,6.6v7.5c0,2.1-2.1,4.7-4.7,5.7c-0.6,0.2-1.1,0.3-1.7,0.3c-1.8,0-3.7-1.1-5.1-2.9c-0.6-0.8-1.7-1.2-3.5-1.2c-0.8,0-1.6,0.1-2.4,0.1c-0.8,0.1-1.6,0.1-2.4,0.1c-3,0-7.2-3.6-8.7-6.6c-1.3-2.7-2.8-4.4-5.8-4.4c-0.5,0-0.9,0.2-1.1,0.5c-0.8,1.1,0.2,3.9,0.7,5.3l0.4,1.2c0.8,2.5,2.9,9,4.2,11.1c1.5,2.5-2.9,9.3-3.4,10.1l-0.2,0.2l-0.3,0.1c-0.7,0.3-6.5,2.9-8.9,2.9c-1.6,0-3.1,3-3.8,5.9c-0.4,2.3-1,6.9-1,8.9c0,0.5-0.2,1.3-1,2.1c-1.3,1.1-3.6,1.8-6.4,1.8c-0.6,0-1.3,0-1.9-0.1c-0.2,0-0.5,0-0.7,0c-1.1,0-2,0.3-2.6,0.9c-0.7,0.7-0.9,1.6-0.9,2.2l-0.1,1.8L426.1,709.9z"
}, {
  id: "b21",
  parentId: "a1",
  name: "kordestan",
  persianName: "کردستان",
  persianNickName: "کردستان",
  ltrRotate: 0,
  ltrX: 185,
  ltrY: 310,
  d: "M214,371.5c-1.5,0-3.1-0.1-4.6-0.4c-2.1-0.3-7.3-0.5-11.5-0.5l-0.6,0l-0.3-0.5c-0.7-1.3-2-3.6-2.8-5.1c-0.5-1-2.2-1.5-4.1-2c-1.7-0.5-3.4-1-4.8-1.9c-3.3-2.2-3.6-8.2-3.6-10.7c0-1.5-1.5-2.6-3.1-3.8c-1.4-1.1-2.9-2.2-3.4-3.6c-0.5-1.6-1.2-2.6-2.1-3c-0.3-0.1-0.6-0.2-1-0.2c-0.5,0-1,0.1-1.6,0.4c-2,0.8-4.3,1.3-5.2,1.5l0.8,1.3l-1.8-0.1h-2l-1.4-0.9l-0.3-1.9l0.7-1.3l0.7-0.8l0.3-0.6l-0.3-1.3l-1.2-1.4l-3.3-2.9l-3.8-6l-0.9-2.3v-0.9l0.2-0.9l0.5-0.7l0.4-0.3l-0.8-1.4l-0.9-2.4l1.4-0.5h0.6l0.7,0.2l-0.4-2.2V313l0.2-1.4l0.5-1.4l1.1-1.1l1.6-0.5l4.1,0.1l1-0.2l3.1-1.6l2.5,0.2l0.8-0.1l0.6-0.6l0.9-1.2l1.8-1.2l0.8-0.6l0.4-0.9l0.1-0.5l-0.2-0.4l-0.6-0.4l-0.7-0.1l-0.7,0.3l-1,0.7l-1.3,0.5l-2.6,0.5l-1.5,0.1l-1.6-0.6l-0.7-0.6l-0.4-0.5l-0.4-0.7l-0.2-1.1l-0.1,0l-1.8-0.6l-0.5-0.1l-0.7,0.3l-1.1,0.6l-1.5,0.5l-3.7-0.2l-1.9,0.6h-0.9l-0.6-0.2H149l-1.2,0.9l-1.5,0.8h-1.7l-1-0.6l-0.3,0l-2.3,0.6l-1.6-0.5l-1-1.3l-1.5-3.5l-2.7-3.5l-1.4-1.3l-1.5-0.3l-0.9-0.6l-0.7-0.6l-2.6-2.2l3,0.4c0.1-1.4,0.5-5.5,0.5-6.7c0-1.7,1.6-4.8,4.3-4.8c2.3,0,2.8-0.3,2.8-3.3c0-3.5,1.9-5.8,4.8-5.8c2.9,0,9,0,10.4-0.5c1.1-0.4,1.8-2.3,1.8-5.3v-8.2l0.8-0.2c1.2-0.3,4.2-0.9,7-0.9c0.8,0,1.7-0.1,2.4-0.2c0.8-0.1,1.4-0.1,1.9-0.1c1.8,0,2.7,0.8,2.9,2.5c0.5,3.2,2.2,3.8,5.8,3.8c2,0,8.7-1,14.1-1.8l0.1,0c4.9-0.7,7.9-1.2,8.8-1.2c2.9,0,5,1.1,6.2,3.1c1.5,2.4,2.9,2.9,5.8,3.4c0.3,0.1,0.7,0.1,1,0.2c2.5,0.4,4.3,0.7,4.7,3c0.4,2.1,2.9,3.3,6.8,3.3c3.4,0,8.3-2.5,9.8-4.9c0.7-1.1,1.1-2.8,1.2-4.9l0.1-1.3l1.2,0.4c0.4,0.1,1,0.3,1.6,0.3c0.4,0,0.8-0.1,1.1-0.2c0.8-0.3,1.3-0.8,1.7-1.7c0.3-0.7,0.7-1.1,1.3-1.3c0.3-0.1,0.6-0.1,1-0.1c1.8,0,4.2,1.3,6.4,2.5c1,0.5,1.9,1,2.7,1.4c3.8,1.6,7.2,2.5,9.9,2.5c2.8,0,4.2,0.2,4.5,0.3l0.4,0.1l0.2,0.4c0.2,0.4,0.7,1.3,0.9,1.8c0.1,0.4,0.5,1.4,0.8,2c0.1,0.2,0.3,0.6,0.3,0.6l0,0.1c0,0.1,0.1,0.3,0.1,1.5c0,0.1,0,0.2,0,0.3c0,0.9,0.1,1.8-0.1,2.4c-0.2,0.6,0.3,2.1,0.6,2.6l0,0.1l0,0.1c0.2,0.4,1.5,3.6,0.7,5.5c-0.3,0.6-0.7,1-1.4,1.3c-2.9,1-3.3,2.4-3.3,3.8c0,0.3-0.1,0.8-0.2,1.5c-0.3,1.7-0.7,4.2,0.2,5.2c0.2,0.2,0.5,0.5,1.3,0.5c0.6,0,1.1,0,1.5,0c0.3,0,0.6,0,0.8,0c1.9,0,2.2,0.9,2.4,2.2c0.5,2.6,1,4.3,3.3,4.3c3.1,0,5.3,0.8,6.2,2.1c0.5,0.7,1.5,2.2,2.5,3.6l0.5,0.7l-0.7,0.6c-1.3,1.1-5.6,5-7,6.4c-1.8,1.8-8.9,2.7-12.2,2.7c-0.4,0-0.7,0.1-0.9,0.3c-0.5,0.7,0.3,2.6,1,4.3c0.7,1.6,1.1,2.7,1.1,3.5c0,1.6,2.3,3.8,3.9,5.4c0.7,0.7,1.3,1.3,1.7,1.8c0.5,0.6,1.3,1.3,2,2c1.1,1,2.3,2,2.7,3.1c0.4,0.9,2.4,3.3,5.1,6l0.3,0.3v8.1c0,1.9-0.3,4.2-0.9,4.9l-0.3,0.3l-0.4,0c-0.2,0-0.4,0-0.6,0c-0.4,0-1,0.1-1.7,0.1c-1.5,0-3.4-0.1-5.6-0.4c-0.4,0-0.7-0.1-1.1-0.1c-4.3,0-6.7,3.2-7,3.6l-0.5,0.7l-1.2-0.6c-1.5-0.7-1.5-2.4-1.5-4c0-0.7,0-1.5-0.2-2.2c-0.5-1.8-6.6-2.8-9.8-2.8h-14c-1.8,0-2.8,2.7-2.8,5.3c0,2.7-2.1,4.3-5.8,4.3c-2.6,0-3.4-0.8-3.6-1.3c-0.7,0.7-2.8,2.5-4.7,3.7c-1.7,1-1.1,3.1,0,6.1c0.2,0.6,0.4,1.1,0.6,1.6c0.2,0.6,0.1,1.1-0.2,1.5C218.7,370.6,217.9,371.5,214,371.5z"
}, {
  id: "b22",
  parentId: "a1",
  name: "lorestan",
  persianName: "لرستان",
  persianNickName: "لرستان",
  ltrRotate: 0,
  ltrX: 275,
  ltrY: 465,
  d: "M354.5,514.1c-0.8-1.5-1.5-2.8-1.9-3.6l-0.3-0.6c-0.9-1.8-2.2-3.2-4.2-4.6c-1.5-1-4.5-1-5.5-1c-0.5,0-1.1,0-1.5,0c-0.3,0-0.6,0-0.9,0c-1.6,0-5.4,0-8.1-1c-2.6-1-6.3-2-7.9-2c-2.3,0-9.6-0.4-11.8-2.4c-1.6-1.4-3.3-2.1-5.3-2.1c-0.5,0-1,0-1.5,0.1c-1.1,0.2-3.7,0.3-6.8,0.3c-3.1,0-6-0.1-7.6-0.3c-0.5-0.1-1.1-0.1-1.6-0.1c-3.2,0-7.5,0.8-9.1,3c-1.6,2.1-4.3,4.7-5.4,5.6l-0.4,0.3l-0.5-0.1c-1-0.2-2.7-0.7-3.2-1.8c-0.6-1.4-3.4-3.3-4.1-3.8c-0.6-0.4-1.2-0.7-1.8-1c-1-0.5-1.4-0.7-1.7-1c-0.2-0.3-0.5-0.6-0.8-0.9c-0.3-0.4-0.6-0.8-0.9-1.1c-0.4-0.4-1.6-1-2.7-1.5l-2.5-0.3l-0.1,0c-0.5-0.2-4.9-1.7-5.6-2.2c-0.2-0.2-0.4-0.3-0.7-0.5c-1.4-1-2-1.5-2.2-1.9c-0.3-0.4-1.1-0.8-1.6-1c-0.2-0.1-0.3-0.1-0.4-0.2c-0.6-0.3-1.3-0.9-1.6-1.7c-0.2-0.7-1.6-2.6-2-3c-0.2-0.1-0.8-0.5-2-0.9l-0.3-0.1l-0.2-0.2c-0.7-0.9-1.4-1.5-1.9-1.7c-0.3-0.1-1.1-0.4-2-0.9c-2.2-1-6-2.6-6.8-2.7c-1.1-0.1-1.5-0.9-1.9-1.6c-0.1-0.1-0.1-0.3-0.2-0.4c-0.5-0.8-1-1.1-1.6-1.5c-0.6-0.4-2.8-2.1-3.2-2.5c-0.1-0.1-0.3-0.4-1.7-0.7c-0.3,0-3.7-0.6-4.4-1.4c-0.8-0.8-1.1-1.4-0.4-2.6c0.2-0.3,0.2-0.7,0.1-1.1c-0.2-0.5-0.6-0.9-1-1c-0.9-0.3-4.7-2.5-4.9-2.6l-0.1-0.1l-2.2-2c0,0-1.1-1.1-1.7-2c-0.5-0.8-1.2-1.6-0.5-2.6c0.2-0.2,0.2-0.5,0.3-0.8c0.1-0.6,0.3-1.2,1.1-1.4c0.6-0.2,1.4-0.2,2.2-0.2c0.8,0,1.1,0.1,1.3,0.2l0.1,0l0.1,0.1c0.3,0.2,0.5,0.4,0.8,0.7c0.3,0.2,0.5,0.5,0.8,0.7c0.3,0.3,1.2,0.4,2.2,0.4l0.1,0l1.5,0.2c0.3-0.8,0.4-1.3,0.3-1.5c-0.2-0.4-0.3-1.1-0.5-1.6l-0.1-0.5l0.3-0.4c0.5-0.5,1.6-1.8,2.1-2.2c0.2-0.1,0.2-0.3,0.2-0.7l0-1.1l1.1,0.1c0.6,0,1.1,0.1,1.6,0.1c0.9,0,1.4-0.1,1.6-0.2c0.5-0.2,1.2-0.6,1.7-1.1l0.5-0.5l0.7,0.4c0.3,0.1,0.7,0.3,1.1,0.3c0.3,0,0.6-0.1,0.9-0.3c1-0.7,1.6-0.9,2.2-0.9c0.3,0,0.6,0.1,0.9,0.3c0.2,0.1,0.9,0.4,2.1,0.4c1.1,0,2.3-0.2,3.2-0.5c3.4-1.3,3.7-2,3.7-2.1l0-0.1l0-0.1c0.1-0.4,0.5-1,2.1-3c0.2-0.3,0.3-0.4,0.4-0.5l0.1-0.1l0.1-0.1c0.1-0.1,0.3-0.3,0.7-0.5c0.6-0.4,1.5-0.9,1.9-1.6c0.6-0.9,0.4-1.6,0.3-2.2c0-0.1-0.1-0.3-0.1-0.4c-0.1-0.4-0.3-1.6-0.7-3.2l0-0.2l0-0.2c0-0.2,0.1-0.9,0.1-1.5l0-0.3l0.1-0.1l-0.1-0.1l-0.1-0.3c0-0.1,0-0.1-0.1-0.2c-0.4-0.8-1.5-2.8-1.7-3.2c-0.2-0.4-1.3-1.6-1.7-1.9l0,0l0-0.1c-0.4-0.5-0.9-2.1-1-2.4l0-0.1v-2.4l0.2-0.3c0.5-0.7,2.4-2.9,3.5-3.6c0.7-0.4,1.6-1.6,2.6-2.7c0.8-1,1.6-1.8,2.1-2.3c1.1-0.9,2.2-4.8,2.3-5.7c0.1-0.6,0.7-2.8,1.1-4l0.4-1.2l3.7,2.2l1.6-0.4l1.5,0.9h7l-0.2,1.2c-0.1,0.8,0,1.5,0.4,2.2c1.5,2.5,2.4,3.4,5.8,3.4c3.7,0,5.7,1,6.2,3.2c0.5,1.9,1.5,5.9,4.4,7.9c2.8,1.9,8.8,4.2,9.4,4.5l0,0c0.2,0,1.6,0.3,3.2,0.3c1.6,0,2.9-0.3,3.6-0.8c0.5-0.3,0.7-0.8,0.8-1.3c0.5-3.7,3.4-4.2,5.7-4.2c0.7,0,1.5-0.1,2.3-0.2c0.8-0.1,1.8-0.2,2.6-0.2c1,0,2.2,0.1,2.8,0.9c0.5,0.7,1.4,1.8,2.2,2.9c0.9,1.2,1.8,2.3,2.3,3.1c0.7,1,3.3,2,5.3,2c0.5,0,0.8-0.1,0.9-0.1c0.5-0.2,1.2-0.4,2-0.8l1-0.4l0.3,1c0.3,1,1.1,3.3,0.8,4.9c-0.1,0.6,0,1.2,0,1.8c0.2,1.2,0.3,2.3-1.1,3.7c-0.4,0.4-1,0.9-1.7,1.4c-1.4,1.1-2.9,2.3-2.7,3.1c0.1,0.3,0.5,0.8,2.2,1.1c5.6,1,7.6,1,10,1c2.8,0,4.3,1,4.3,2.9c0,1.5,1.5,4,2.3,5.1c0.3,0.1,1.9,0.8,3.5,0.8c1.5,0,2.5-0.5,3.1-1.7c0.5-1,0.9-2.1,1.2-3c0.6-1.7,1-2.8,1.8-3.2c0.2-0.1,0.4-0.1,0.6-0.1c0.3,0,0.5,0.1,0.8,0.2c2.3,1,3.9,1,6.2,1c0.4,0,0.9,0,1.5,0c0.5,0,1.1-0.1,1.7-0.1c1.6,0,2.4,0.2,3,0.7c0.3,0.3,0.4,0.6,0.4,1c0,0.4,0,0.9-0.1,1.4c-0.2,2.2-0.4,4.9,1.3,6.4c2,1.7,6.1,3.9,7.3,4.5l0.4,0.2l0.1,0.5c0.3,1.5,0.7,3.3,0.9,3.9c0.1,0.2,0.1,0.5,0.2,0.8c0.4,2.2,0.9,3.4,2.3,3.4c0.9,0,1.7,0,2.4,0.1c0.6,0,1.2,0.1,1.6,0.1c0.6,0,1,0,1.2-0.1c0.5-0.2,1.4-0.6,2.6-1.3l1.1-0.6l0.3,1.2c0.5,1.6,0.9,3.8,0.3,5.7c-0.8,2.3-1.6,2.9-3.1,3.9c-0.4,0.2-0.8,0.5-1.3,0.9c-0.5,0.4-1.1,0.7-1.7,1c-1.3,0.7-2.2,1.2-2.2,1.9c0,0.2-0.1,0.8,1.2,2c3,2.7,4.3,4.1,4.4,5.2c0,0.3-0.1,0.6-0.4,0.9c-1,1-2.1,2.1-5.5,2.1c-3,0-7.5-0.3-8.6-0.3c-0.6,0.5-1.5,1.5-1.5,2.4c0,0.7-0.1,2-0.2,3.3c-0.1,1.4-0.2,2.7-0.2,3.3c0,0.9,0.5,2.4,0.9,3.4l0.1,0.2l0,0.2c0,0.4,0.1,1.9,0.6,3.4l0.3,0.8l-0.8,0.4c-1.3,0.6-5.5,2.7-7.2,3.8c-2,1.3-5.3,3-5.4,3l-1,1L354.5,514.1z"
}, {
  id: "b23",
  parentId: "a1",
  name: "markazi",
  persianName: "مرکزی",
  persianNickName: "مرکزی",
  ltrRotate: 0,
  ltrX: 350,
  ltrY: 420,
  d: "M381,468.2c-0.5,0-1.1,0-1.6-0.1c-0.7,0-1.5-0.1-2.4-0.1c-2.1,0-2.5-2.3-2.7-3.7c-0.1-0.3-0.1-0.6-0.2-0.8c-0.3-0.8-0.7-2.7-1-4.2c-0.8-0.4-5.4-2.8-7.6-4.6c-1.9-1.7-1.7-4.6-1.5-6.7c0-0.5,0.1-1,0.1-1.4c0-0.3-0.1-0.5-0.3-0.6c-0.6-0.6-2.1-0.6-2.6-0.6c-0.6,0-1.2,0-1.8,0.1c-0.5,0-1,0-1.5,0c-2.4,0-4.1,0-6.4-1c-0.2-0.1-0.4-0.1-0.6-0.1c-0.1,0-0.2,0-0.3,0.1c-0.6,0.3-1,1.4-1.5,2.8c-0.3,1-0.7,2.1-1.2,3.1c-0.4,0.9-1.4,1.9-3.6,1.9c0,0,0,0,0,0c-1.5,0-2.9-0.5-3.5-0.7l-0.3-0.1l-0.2-0.3c-0.4-0.6-2.2-3.4-2.2-5.3c0-0.6,0-2.4-3.8-2.4c-2.3,0-4.4,0-10-1c-1-0.2-2.4-0.5-2.6-1.4c-0.2-0.9,0.4-1.6,2.9-3.6c0.6-0.5,1.2-1,1.6-1.4c1.2-1.2,1.1-2.1,1-3.3c-0.1-0.6-0.2-1.2,0-1.9c0.2-1-0.1-2.8-0.8-4.7l-0.3-0.9l0.9-0.3c1.7-0.6,2.8-1,3.6-1.2c1.4-0.4,4-2.2,4.7-4.1c0.3-0.8,0.2-1.4-0.3-2c-1.8-2.2-4.3-9-5-11l0-0.1l-2.5-8.5c-0.2-0.9-0.9-4.9,1-7.3c0.8-1,1.2-2.1,1.5-3.1c0.5-1.6,1-2.9,2.7-2.9c2.1,0,3.3-2.1,3.3-4.3c0-1.9-0.4-7.7-0.5-8.4l0-0.2l0-0.2c0.5-1.7,3-10.1,8.2-10.1c7.4,0,8.3-2.6,8.3-3.8c0-1.8,1-4.8,1.7-7.1c0.3-0.9,0.6-1.9,0.8-2.5c0.1-0.4,0.2-0.8,0.4-1.3c0.5-1.3,1-2.9,0.5-4c-0.2-0.4-0.6-0.8-1.2-1c-1.9-0.6-4.1-1.6-4.7-3.2c-0.3-0.8-0.1-1.7,0.6-2.7c1.6-2.4,3.5-6.3,4.2-7.8l0.4-0.8l0.8,0.3c0.6,0.2,1.4,0.3,2.4,0.3c1.4,0,3.1-0.2,4.9-0.5l0.5-0.1c3.3-0.5,4.8-3.7,4.8-5.2l0-0.3l0.2-0.3c1-1.4,7.2-2.2,9.6-2.2c2.6,0,7.1,0.5,11.1,2c0.7,0.2,2,0.5,4.7,0.5c5.2,0,11.5-1,11.6-1l0.1,0l0.1,0c0.1,0,10-0.5,12.5-0.5c0.5,0,1,0,1.5,0c0.6,0,1.3,0,1.9,0c1.7,0,4.1,0.1,6.7,1.1c1,0.4,2,0.8,2.9,1.2c3,1.3,6.4,2.8,10.5,2.8c1.5,0,2.5,0.4,3.1,1.2c1.1,1.3,0.6,3.4,0.3,4.9c-0.1,0.5-0.2,0.9-0.2,1.2c0,0.6-0.3,1.7-0.7,3.3c-0.6,2.3-1.3,5.1-1.3,7.2c0,2.5-1.5,3.1-2.9,3.5l-0.5,0.1l-0.2-0.2l0,0.2l-0.6,0.2c-0.3,0.1-0.6,0.2-0.9,0.4c-2,1-6.2,4.7-8.4,7c-2.5,2.5-0.7,7.9,0.1,10.2c0.2,0.7,0.5,1.7-0.1,2.3c-0.4,0.5-1.2,0.7-2.6,0.7c-1.1,0-2.5-0.1-3.6-0.2c-0.9-0.1-1.6-0.1-2.3-0.1c-3.7,0-5.7,1.2-6.5,3.9c-0.3,1-0.9,1.7-1.8,2.1c-0.6,0.3-1.4,0.4-2.3,0.4c-2.3,0-4.8-1-5.8-1.4c-3-1.3-6.4-1.8-7.2-2l-1.4,4.3l0,0c0,0-1,6.4-2,9c-0.9,2.2-0.2,5,2,8.3c1.9,2.9,6.4,2.9,9.3,2.9c3.3,0,3.3,2.8,3.3,5.8c0,1.4,0.9,2.5,1.8,3.8c1.1,1.4,2.2,2.8,2.2,4.7c0,0.8,0.2,1.4,0.7,1.7c0.3,0.2,0.8,0.3,1.3,0.3c0.7,0,1.3-0.2,1.6-0.3l0.1,0l0.2,0c0.7,0,4.1-0.1,6.3-1c0.8-0.3,2.1-0.5,4-0.5c2,0,4.2,0.2,6,0.3c1.3,0.1,2.4,0.2,3.1,0.2c2.4,0,3.5,2.2,4.5,4.1l0.3,0.5c1,2,4.9,5.9,6.9,7.4c1.3,1,1.1,3.7,0.4,7.7c-0.2,0.8-0.3,1.6-0.3,2c0,5-0.3,8.4-1,10.1c-0.9,2.2-4.9,4.1-8.5,4.1c-1,0-2-0.2-2.8-0.5c-1.2-0.5-2.5-0.7-3.8-0.7c-2.3,0-4.5,0.8-5.4,2.1c-1.5,2.1-6.1,3.6-10.7,3.6c-0.8,0-1.5,0-2.3,0c-0.7,0-1.4,0-2.1,0c-2.9,0-5.4,0.3-7.6,1.5c-1,0.5-1.9,1.2-2.8,1.8l-0.1,0.1c-2.5,1.7-5,3.4-8.7,4.2c-4.5,0.9-5.2,6.6-5.3,7.2c0,0,0.4,0.9,0.4,0.9l-0.8,0.4c-0.8,0.4-2.2,1.2-2.9,1.4C382,468.2,381.6,468.2,381,468.2z"
}, {
  id: "b24",
  parentId: "a1",
  name: "mazandaran",
  persianName: "مازندران",
  persianNickName: "مازندران",
  ltrRotate: 0,
  ltrX: 505,
  ltrY: 270,
  d: "M514.4,306.1c-1.9,0-3.7-0.4-6.1-2.1c-1.3-0.9-2.8-1.5-4.3-2.1c-2.4-0.9-4.7-1.8-5.3-4.1c-0.9-3.3-2.8-6.3-4.9-7.9c-0.8-0.6-2.6-1.5-4.6-2.5c-2.9-1.4-6.2-3.1-7.9-4.5c-1.8-1.5-3.8-2.7-5.7-3.3l-0.1-0.1l0,0l-0.1,0l-0.2,0c-1-0.3-1.9-0.5-2.7-0.5c-2.7,0-8.6-0.5-10.6-1l-0.5-0.1c-4.4-1.1-10.5-2.7-12.6-4.4c-1.7-1.4-7.4-4.4-12.1-6.8l-0.5-0.3l0-0.6c-0.1-3.4-1.1-7.5-3.4-8.9c-1-0.6-2.9-1.9-5.1-3.4c-4.9-3.4-12.4-8.6-14.8-8.6c-0.8,0-1.8-0.2-3.3-0.7l-1.7-0.5l1.4-1.2c2.7-2.3,5.8-5.3,6.4-7c1-2.5,4-9,4-9l2.9-6.9c0,0,0.4-1.4,0.4-1.4l3.8,2.4l1.1,0.2l1.1,0.5l1.9,1.8l0.7,0.7l9.2,4.7l8.4,5.7l4.7,2l16.3,3.1l10.5,2.8l10.7,1.9l10.3,2.8l10.6-1.3l9.6-3.4L532,240l10.4-1.9l10-1.9l9.9-2.9l9.7-2.8l19.5-4.1l2.7-0.4l23.1-1.3l3.9-0.8l4.3-3.6l-0.2,5.5l-4.1,1.4l-4.2,0.5l-2.6,0.8l-0.9,0.4l-1.1-0.1l-1.5-0.4l-0.6,0.1l-1.6,0.6l-1.1,0.3l-3.1-0.5l0.1,0.9l-0.2,0l0.3,0.4l2,0.8h0.1l11.9,1.1l-3,1.5c0,0.8,0.1,4,0.5,5.8c0.4,1.5,2.3,2.8,3.4,3.4c1,0.4,6.2,2.6,8.9,3.5c0.9,0.3,1.5,1,2,2c0.9,2.2,0.4,5.5-0.3,6.9c-1.1,2.2-6.5,3.7-8.2,4.1c-1.1,0.3-2.1,1.8-2.6,3.2c-0.4,1-0.6,2.3-0.2,2.9c2.2,3.3,0.6,5.4-0.6,6.3c-2.1,1.7-11.4,9.8-14.8,12.8l-0.3,0.2l-0.3,0c-1.4,0.1-8.6,0.5-11.3,0.5c-2.8,0-5.8,1.4-8.3,3.9c-0.8,0.8-1.5,1.8-2.1,2.7c-1.5,2.1-3,4.3-5.5,4.3c-2.7,0-7.9,2.5-10.3,3.9l-0.4,0.6l-0.8-0.2c-0.4-0.1-0.8-0.2-1.1-0.4c-1.1-0.4-3.1-0.8-5.4-1.3c-4.6-1-8.2-1.8-9.7-2.7c-1.4-0.8-5.8-2-9.7-2c-1.2,0-2.1,0.1-2.9,0.3c-0.8,0.2-1.4,0.6-1.6,1.1c-1.5,3.1-6.1,6.6-8.6,8.1c-2.6,1.6-6.7,2.5-9.1,2.5c-0.3,0-0.6,0-0.9,0l-0.1,0C515.1,306.1,514.7,306.1,514.4,306.1z"
}, {
  id: "b25",
  parentId: "a1",
  name: "ghazvin",
  persianName: "قزوین",
  persianNickName: "قزوین",
  ltrRotate: -60,
  ltrX: -80,
  ltrY: 470,
  d: "M357.5,328.7c-1.3,0-2.3-0.2-3.1-0.6c-0.6-0.3-1.4-0.7-2.2-1.1l-0.1,0c-2.2-1-4.6-2.2-5.7-2.9c-1-0.6-2.3-1.4-3.8-1.4c-0.7,0-1.3,0.1-2,0.4c-0.6,0.2-1.1,0.3-1.7,0.3c-0.7,0-1.3-0.2-1.9-0.6c-0.8-0.6-1.3-1.5-1.3-2.5c0-0.2,0-0.5,0-0.7c0.1-1.9,0.1-3.4-2.4-5.1c-3.1-2.1-9-6-11-7c-1.6-0.8-6.8-2-8.3-2.3l-0.8-0.2l0-0.8c0.2-3.9,0.9-6.4,2-7.5l8.1-8.1l0.6,0.3c0.6,0.3,2,1.1,4,2.8c1.4,1.1,3.4,2.5,5.1,2.5c0.1,0,0.2,0,0.4,0c0.7-0.1,1.2-0.4,1.6-0.9c0.4-0.5,0.7-1.1,1-1.8c0.8-1.6,1.6-3.5,4.7-3.8c4-0.5,7.8-2.5,8.3-4.3c0.1-0.6,0.4-1.5,0.8-2.9c0.9-3,2.2-7.2,2.2-8.6c0-1.7-1.1-4.9-1.7-6.6l-0.3-0.8c-0.7-2.2-2-3.6-3.9-4.4c-0.7-0.3-1.4-0.6-2.2-1c-1.8-0.8-3.7-1.7-5.8-2l-0.5-0.1c-3-0.5-6.7-1.1-8.2-4.1c-1.5-3-2.6-7.1-1.5-8.8c0.7-1.1,2-4.6,2.9-7.3l0-0.1l2.9-4l0.7,0.3c1.6,0.6,2.9,1,3.5,1.1c1.5,0.2,3,0.4,3.6,1.4c0.5,0.8,1.3,1.3,2.3,1.5c0.3,0,0.6,0.1,1.1,0.1c0.6,0,1.2,0,1.4-0.1l0,0h3.4l0.3,0.3c1,1.1,1.7,1.9,2.1,2.4c1.6,2.1,5.6,4.4,8.8,4.4c1.8,0,3.5,0.7,5.3,1.5c1.7,0.7,3.5,1.5,5.2,1.5c3.7,0,12.5,0,15.5-0.5c2.4-0.4,7.5-3.1,10.2-4.6c0.7-0.4,1.3-0.7,1.7-0.9c0.2-0.1,0.5-0.2,0.9-0.2c1.3,0,3.5,0.8,6.1,1.8c2.4,0.9,5.1,1.9,6.6,1.9c2.4,0,8.5,4.1,15.1,8.7l0.1,0.1c2.1,1.5,3.9,2.7,4.9,3.3c3,1.7,3.5,7.2,3.6,8.9l0.1,1.1l-1.1-0.1c-2.4-0.2-6.7-0.6-8.2-0.9c-0.7-0.2-2-0.4-4.6-0.4c-2,0-4.4,0.1-6.8,0.4c-1.1,0.1-1.8,0.5-2.2,1.1c-0.8,1.3,0.3,3.6,0.9,5.1l0.1,0.1c0.2,0.4,0.3,0.7,0.4,0.9c0.4,1.3,6,3.7,9.3,5.1l0.5,0.2c1,0.4,1.7,1.1,1.9,1.9c0.4,1.4-0.5,3-0.7,3.3l-0.1,0.2l-0.1,0.1c-0.6,0.5-3,2.1-6.5,3c-2.8,0.7-6,5.1-8.1,8c-0.9,1.3-1.7,2.4-2.3,3c-0.7,0.7-1.6,1.4-2.5,2.1c-1.9,1.5-3.9,3-3.9,4.2c0,2-1,7.6-3.1,8.7c-0.8,0.4-1.4,1.3-1.4,2.3c0,1,0.5,1.9,1.4,2.3c1,0.5,2.4,1.5,4.2,2.9l1.8,1.5l-2.3,0.3c-2.3,0.3-6.6,0.8-10.1,0.8c-2.2,0-3.8-0.2-4.8-0.6c-3.9-1.5-8.3-2-10.9-2c-4,0.1-9.3,1.2-9.3,2.3c0,1.5-1.5,5.2-5.2,5.7l-0.5,0.1C360.7,328.4,359,328.7,357.5,328.7z"
}, {
  id: "b26",
  parentId: "a1",
  name: "ghom",
  persianName: "قم",
  persianNickName: "قم",
  ltrRotate: 0,
  ltrX: 450,
  ltrY: 380,
  d: "M438.9,414.3c-1-2.1-2-3.7-4-3.7c-0.7,0-1.8-0.1-3.1-0.2c-1.9-0.1-4.1-0.3-6-0.3c-1.8,0-3.1,0.1-3.8,0.4c-2.3,0.9-5.9,1-6.5,1l-0.1,0c-0.3,0.1-1,0.3-1.8,0.3c-0.6,0-1.1-0.1-1.6-0.4c-0.6-0.4-0.9-1.2-0.9-2.1c0-1.7-1-3.1-2.1-4.4c-1-1.3-1.9-2.5-1.9-4.1c0-3.6-0.3-5.3-2.8-5.3c-3,0-7.6,0-9.7-3.1c-2.3-3.4-3-6.4-2-8.7c1-2.4,1.9-8.6,2-8.9l0-0.1l1.6-4.7l0.8,0.1c1.5,0.2,4.3,0.8,6.9,1.9c1,0.4,3.4,1.4,5.6,1.4c0.8,0,1.5-0.1,2.1-0.4c0.8-0.4,1.2-0.9,1.5-1.8c1.1-3.9,4.5-4.3,7-4.3c0.7,0,1.4,0,2.2,0.1c1.3,0.1,2.6,0.2,3.6,0.2c1.2,0,1.9-0.2,2.2-0.6c0.3-0.4,0.3-0.9,0-1.9c-0.8-2.4-2.7-8,0.1-10.8c2.7-2.7,6.6-6.1,8.6-7c0.5-0.3,1-0.4,1.7-0.6l0.4-0.1l0.4,0.2c0.9,0.6,2.6,1.5,4.6,1.5c1.2,0,2.4-0.4,3.4-1.1c2.9-1.9,7.1-2.2,9.4-2.2c2.8,0,5.6,0.5,7.4,1.2c2.4,1,8.4,2.4,13.3,3.4l0.8,0.1l0.1,0.8c0.1,0.8,0.5,2.6,3.4,3.7c1.5,0.6,3.6,1.1,5.4,1.6c4.3,1.1,6.1,1.7,6.7,2.5c0.6,0.8,4.1,3.8,9,7.6l0.6,0.4l-7.1,22.8l-0.5,0.2c-1.2,0.4-7.3,2.4-8.7,2.4c-1,0-6.7,1.2-11.9,2.5l-0.1,0l-0.1,0c-0.9,0.1-8.6,0.5-11.9,0.5c-3.6,0-6.5,0.5-7.9,1.5c-1.4,0.9-7.5,3.6-8.4,4c-0.1,0.6-0.5,2.8-0.5,5.8c0,0.9,0.1,1.6,0.1,2.3c0.2,2,0.3,3.2-1.7,4.5c-1.7,1-3.5,1.8-4.4,2.2l-0.9,0.4L438.9,414.3z"
}, {
  id: "b27",
  parentId: "a1",
  name: "semnan",
  persianName: "سمنان",
  persianNickName: "سمنان",
  ltrRotate: 0,
  ltrX: 655,
  ltrY: 330,
  d: "M554.1,404.9c-3-2-7-4.6-8.8-5.3c-0.9-0.3-2.4-0.9-4.2-1.6l-0.2-0.1c-3.4-1.3-7.3-2.7-8.6-3.4c-0.5-0.2-1.4-0.5-3.2-0.5c-2.5,0-6,0.6-9.2,1.5c-1.6,0.5-3.7,0.7-5.9,0.7c-4.3,0-8.8-0.9-10.8-2.3l-7.7-5.1l7.1-22.7l0.1-0.2c2.7-2.9,5.3-6.6,5.3-8.2c0-2.5,0-5.4-1.9-7.3c-1.9-1.9-4.5-5-5.5-7.1c-0.6-1.2-2.3-5.3,0-8.3c1.9-2.3,2.5-5.2,1.5-7.2c-0.6-1.2-2.4-5.9-0.8-7.4c0.2-0.2,0.7-0.5,1.4-0.5c0.8,0,1.9,0.4,3.3,1.1c7.5,4,10,5,12.5,6c1,0.4,1.9,1.2,2.9,2c1.6,1.3,3.3,2.9,6,3.5c1.2,0.3,2.4,0.4,3.6,0.4c3.6,0,6.1-1.1,6.6-2.3c1.1-2.3,6.7-8.2,12.1-10.6c3.5-1.6,6.6-4.2,9.1-6.4c1.3-1.1,2.5-2.1,3.3-2.6c1.4-0.9,2.5-2,3.5-3.1c0.7-0.8,1.3-1.5,2-1.9c1.1-0.7,2.8-2.6,3.7-3.7c-0.8-0.2-3-0.8-5.2-1.5l-2.3-0.7l2.1-1.1c2.5-1.3,7.1-3.6,9.8-3.6c2.3,0,3.6-2,5.1-4.1c0.7-1,1.4-2,2.2-2.8c2.6-2.6,5.7-4.1,8.7-4.1c2.8,0,10.5-0.4,11.4-0.5c1.6-1.4,12.6-11.1,14.9-13c2.3-1.8,1.5-4.1,0.4-5.7c-0.5-0.7-0.4-2,0.2-3.4c0.6-1.5,1.7-3.2,3-3.5c3.9-1,6.7-2.3,7.7-3.6l0.3-0.4l0.5,0c1.1,0,6.7-0.2,11.3-0.2c3,0,4.9,0.1,5.9,0.2c0.2,0,0.5,0.1,0.8,0.1c3.6,0,10.4-2.4,12.9-4.5c0.9-0.8,1.6-1.6,2.3-2.3c1.2-1.4,2.1-2.2,3.1-2.2c0.4,0,0.9,0.1,1.4,0.4c0.5,0.3,1.1,0.5,1.8,0.5c0.4,0,0.9-0.1,1.4-0.2c2.3-0.6,4.6-2.6,6-5.2c2.5-4.6,8.7-6.6,13.7-6.6h12.9l0.2-0.2c5.7-4.1,7.6-5.4,8.2-5.8c1-0.7,3.9-3.9,6.4-6.9c-0.1-1.1-0.8-10.2,2.7-11.6c2.9-1.3,4.3-3.3,4.3-6.3c0-2.8,3.6-5,5.1-5.7c1.8-0.9,4.8-1.8,5.4-2l0.1,0h2.3l0.5,9h4.3c2.2,0,2.3,5.6,2.3,6.3c0,3.1-0.8,5.4-2.6,7.7c-1.6,2-1.5,5.1-1.5,7.8l0,0.1c0,0.5,0,0.9,0,1.4c0,0.8,0.3,1.4,0.7,1.6c0.2,0.1,0.3,0.1,0.5,0.1c0.8,0,2-0.6,2.8-1.4c1.3-1.3,7.4-3.9,9.3-4.7l1-0.4l1.1,3.8c0,0,0,0,0,0c0,0,2,4.4,3.9,6.4c1.9,1.9,2.9,5.4,3,6.1c0.4,0.4,3.7,3.9,8.3,4.4c1.3,0.1,2.4,0.2,3.2,0.2c2.1,0,3.2-0.4,5-1l0.6-0.2c1.5-0.5,1.9-1,2.3-1.3c0.5-0.5,0.9-0.7,1.8-0.7c0.5,0,0.9,0.2,1.2,0.5c0.7,0.7,0.7,2,0.6,3.5c0,0.3,0,0.6,0,0.8c0,0.7,1,1.5,1.9,2.2c1.1,0.9,1.8,1.5,2.1,2.2c0.5,1.4,0.5,6.2,0.5,7.2l0,0.5l-8.9,6.9l7.4,9.9L785,288l0.4,9.7l0.1,0.1c4.4,3.7,14.7,12.6,16.2,14.4c2,2.4,4.1,7.1,1.8,10.5c-1.5,2.2-0.7,6.5-0.1,9.7c0.3,1.4,0.5,2.5,0.5,3.3c0,2.9-4.1,3.9-7.5,3.9c-3.6,0-6.4,1.4-7.1,2.4l-0.2,0.3c-1,1.6-4,6.4-10.2,6.7c-4.4,0.2-7.6,2.1-9.2,5.3c-1,1.9-3.1,5.7-5.1,7.7c-1.2,1.2-4,4.7-6.2,7.4c-1.9,2.4-3.7,4.6-4.4,5.3c-1,1-8.7,14.8-15.4,27.2l-0.3,0.5l-84.5,1.5l-99.4,1.2L554.1,404.9z"
}, {
  id: "b28",
  parentId: "a1",
  name: "svab",
  persianName: "سیستان و بلوچستان",
  persianNickName: "سیستان و بلوچستان",
  ltrRotate: 0,
  ltrX: 955,
  ltrY: 870,
  d: "M1048.1,1040.9l-2.6-1.1l-0.4-0.8l-0.4-1.4l-9.3-3l-9.5-1.7l-8.1-2.1l-5.8-0.7l-2.2-1.5l1.2-1.1l-1-1.6l-0.3-1.3v-3.7l-0.1-0.2l-2-2.1l-0.6-0.4l-0.7-0.1l-0.8,0.1l-3.9,1.2l-0.6,0.4l-0.4,0.8l-0.9,1.1l-0.3,0.5l0.2,0.3l0.1,0.9h0.1l0.6,0.4h0.4l0.9,0.3l0.4,1.1v0.6l1.2,2.2l0.7,2.4h-2.4l-1.1-0.3l-3.5-3.4l-0.9-0.5l-3.1-0.5l-2.2-1.7l0.6-1.1l-0.4,0l-2,0.1l-1.3,0.3l0,0l-0.1,0.1l0.1,0.2l-0.2,0.9l-0.4,1.6l-1.2,1.2l-1.8-1.2l-0.4-0.2l-2-0.3l-0.9-0.5l-0.8-1.2l-0.2-0.6l0-0.2h-0.2l-2.3-0.6l-2.2,0.1l-4.5,1.3l-0.1,0.1l-0.4,0.7l-1.3,0.3l-2.8-2.7l-0.3-0.6l-0.3-0.9l-0.4-0.2l-10.2,1.1h-2.6l-2.8-1.3l-3.5-3.7l-2.1-0.8l-2.3,0.1l-8.3,3.1l-1.8,0.2l-2.3,0.4v-1.4l0,0l0-0.4c0.5-10.9,0.8-17.9,0.8-19.5c0-2.6-1-4.5-1.8-6l-0.3-0.6c-0.8-1.7-5-7.5-6.6-8.7c-1.3-1-3.6-2.9-3.5-4.6c0-0.7,0.4-1.2,1-1.6c2.6-1.7,3.1-2.5,1.6-5.1c-1-1.8-3.4-7.5-5.3-12.1l-0.1-0.3c-1.3-3.2-2.4-5.9-2.9-6.9c-1.2-2.3-2.6-10.4-2.9-12l-0.1-0.7l0.6-0.3c0.6-0.3,1.1-0.7,1.6-1.1c0.9-0.7,1.8-1.3,2.7-1.3c1.4,0,4-0.3,4.8-0.4c-0.1-1.4-0.8-7.9-0.8-9.4c0-4.6-0.9-7-2.7-7.3c-3.1-0.4-6.1-4.8-6.5-6.5c-0.4-1.8,0-2.7,1.3-5.2c1.2-2.4,0.4-4.7-0.4-6.9c-0.3-0.7-0.9-1.9-1.5-2.9c-1.4-2.6-2.3-4.5-2.3-5.6c0-1.7,0.8-6.8,0.8-6.8l3.3-30.6c0-0.8,0.8-21.9,1.3-23.4c0.1-0.2,0.1-0.4,0.2-0.7c0.6-2.3,2.1-8.3,6.8-8.3c5.4,0,6.5-1,6.5-2.7v-10.4l-4.2-5c0,0,0,0,0,0c0,0-0.6-0.7-0.5-1.5c0.1-0.7,0.8-1.3,1.9-1.8c2.5-1.1,4.9-2.7,5.6-3.2l0.3-0.2l0.4,0c1.7,0.1,17,1.2,19,1.2c0.5,0,2.3-0.1,2.8-1c0.3-0.5,0.1-1.2-0.4-2c-1.7-2.5-1.3-19.3-1.3-20.3c-0.7-5.2-1.7-9.2-2.4-9.9c-1.4-1.4,0.4-4.6,2.1-6.2c0.8-0.8,1.1-3.1-1.7-9.8c-1.3-3-2.5-13.2-2.5-15.2c0-1-0.7-12.7-1.5-23.9l-0.2-2.7c-0.8-12.4-1.3-20.5-1.3-21.3c0-0.9,0.4-14,1.3-15.6c0.4-0.6,1.1-3.7,1.6-9.2l0.1-0.6l27.7-11.3c0.2-1.4,0.8-6.4,0.8-7.8l0-0.4c0-1,0-2.2,0.8-3c0.6-0.7,1.7-1,3.2-1c4,0,10.3-0.8,11.6-1.6c0.5-0.3,5-3.4,4.1-6.4c-0.2-0.7-1.8-6.6,0-9.6c0.5-0.9,1.3-1.4,2.3-1.6c1.8-0.4,5.1-1.3,8.3-2.2c5-1.4,8.3-2.4,9.4-2.4c2.1,0,5.9-1.8,7.8-3.7c1.6-1.6,4.6-6.9,6.2-9.9l-0.2-1.2l1.3,0.1l14.4,2.1l31.5,4.7l1.8,0.7l1.3,1.1l2.3,2.9l0.5,1.7l-0.4,3v1.1l0.5,1.1l1.6,2.6l0.6,1.8l0.1,2.1l0.1,0.5l0.9,2.1l0.9,2.5l0.2,1.6v1.5l-0.5,1.7l-1,1.9l0.2,0.5l0.2,5.5l-0.5,0.3l-0.1,0.7l0.3,1.1l-1.4,1.5l-18.9,23.3l-28.3,34.5l-7.3,8.8l7.3,8.9l17.5,21.6l1,0.8l1.2,0.5l1.4,1l0.6,2.3l-0.1,1.6l-0.7,2.5v1l0.5,1.1l1.9,2.1l0.8,1.4l0.3,1l0.2,1.6l0.2,0.5l0.3,0.4l0.2,0.1l0.5,0.1l1.1,0.5l0.8,1.4l0.3,1.3l0.2,0.6l0.7,0.4l0.9,0.6l0.4,1.2l-0.4,1.3l-0.8,0.6l-0.1,0.1l0.7,0.3l0.9,0.8l0.6,0.9l2.4,6l0.5,1.5l0.1,1.2l0.2,0.7l1.7,1.9l1.7,3.8l1.6,1.9l6,5.7l2.5,3.3l3.7,3.6l1.7,2.1l0.8,0.5l3.5,1l2.8,1.7l1.6,0.5l3.8,0.3l2,0.4l4.9,2.3l7.7,1.6l2,1.1l0.8,1l0.5,1l0.4,0.6l0.7,0.4l1,0.3l0.9,0.6l0.6,1l0.4,1.2l0.7,1.3l3.5,4l0.7,0.4l9.6-2l2,1.3l0.4,3.1l-1.8,14.8l2.6,11.3l2,23.3l-0.4,3.1l-2.8,6.9l0.8,1.1l0.4,1l-0.1,1.5l-0.3,1.1l-0.4,1.1l-0.4,0.4l1.2,1.1l0.5,0.3l0.6-0.4l0.9-0.2l0.9,0.3l1.3,0.8l1.5,0.3l1.4-0.1l3.3-0.7l1.6-0.3l3.1-1h1.8l1,0.1l0.5-0.1l3.3-1h1l1,0.4l1.7,1.5l0.4,0.4l1.5,0.5l0.7,0.6l0.7,0.8l1,1.4l3,6.8l-3.1-1.1h-0.8l-0.7,0.4l-0.4,0.7l-0.2,0.8l-0.7,0.9l-0.1,0.4l-0.1,0.6l0.3,7.6l0.4,1.1l0.7,1.1l0.6,1.4l-0.2,2l-1.4,1.3l-2.5,0.4l-0.5,0.3l-0.2,0.6l-0.5,9.9l-0.7,3.2l-1.8,1.8h-1.4l-0.6-0.5l-0.4-0.2l-0.3-0.1l-0.2,0l-1.6,0.4h-2.5l-2.3-0.4l-13.7-0.4l-0.2,0.1l-0.2,0.3l-0.7,1.3l-1.1,0.8l-0.7,0.3l-2,0.4h-0.9l-0.8-0.4l-0.1,0l0,0l-0.4,0.5l-0.6,0.6l-1.6,0.5l-9.7,1.1l-0.4,0.1l-0.1,0.1l-0.4,0.9l-0.8,0.6l-0.9,0.2h-1.6l-0.2,0.1l-0.8,0.7l-0.7,0.3l-0.9,0.4l-0.3,0.3l-0.2,0.2l0,0.1l0.1,0.1l0.3,0.5v1l-0.8,1.5l-1.8,1.9l-0.2,0.4l0.2,1.2l0.6,1.4v1.8l-2.1,1.1l-2.5-0.4l-2.6-1l-1.5-0.2l-0.5,0.9l-0.3,1.8l-0.9,1.2l-2.7,0.5l-1,0.3l-1,0.6l-2.1,1.4l-7.1,2.2l-1.1,0.8l-0.7,1.6l-0.5,2l-2.9,22.8l-0.5,1.4l-1.2,1.6l-1.5,0.3h-1.1l-0.8,0.2l-0.8,1.3l0.3,2.1l0.7,2.8l-0.2,2.8l-0.6,0.9l-0.8,0.9l-0.2,0.4l-0.1,0.7l-1.3,22.8l-2.2,6.7l0.5,0.5l-0.6-0.1l-0.6,1.8l-0.6-1.9l-2.6-0.4l0.7,0.9l-0.6,1.4l-1,1.3l-0.1,0.4v0.5l-0.3,0.6l-0.7,0.7l-1,0.6l-1.6,0.5l2.4,2.7L1048.1,1040.9z M1067,1033.3l-0.1-0.8l-0.4-0.3l0,0.3L1067,1033.3L1067,1033.3z"
}, {
  id: "b29",
  parentId: "a1",
  name: "tehran",
  persianName: "تهران",
  persianNickName: "تهران",
  ltrRotate: 0,
  ltrX: 460,
  ltrY: 320,
  d: "M502.2,366.1c-1.3-1-8.1-6.3-9-7.6c-0.6-0.8-3.5-1.6-6.4-2.3c-1.9-0.5-3.9-1-5.5-1.6c-3.5-1.3-3.7-3.8-3.7-4.5c-1.8-0.3-10.6-2.1-13.8-3.5c-1.7-0.7-4.4-1.2-7.2-1.2c-3.7,0-7,0.8-9.1,2.1c-1.2,0.8-2.4,1.2-3.7,1.2c0,0,0,0,0,0c-1.2,0-2.4-0.3-3.6-0.9l-1.8-0.9l1.8-0.9c0.7-0.3,1.5-0.9,1.5-2.6c0-2.2,0.7-5,1.3-7.3c0.4-1.5,0.7-2.7,0.7-3.2c0-0.3,0.1-0.7,0.2-1.3c0.3-1.3,0.7-3.3-0.2-4.5c-0.5-0.6-1.4-1-2.8-1c-4.2,0-7.5-1.4-10.7-2.8c-0.9-0.4-1.9-0.8-2.9-1.2c-2.5-0.9-4.8-1.1-6.4-1.1c-0.7,0-1.3,0-1.9,0l-0.1,0c-0.5,0-1,0-1.4,0c-1.1,0-3.5,0.1-7.4,0.3l-2.5,0.1l1.7-1.7c0.1-0.9,0.8-7.1,4.7-7.6c0.7-0.1,1.5-0.2,2.3-0.3c3.9-0.5,8.9-1.2,14.2-1.2c4.4,0,8.5-0.2,11.2-0.4c1.3-0.1,2.3-0.1,2.8-0.1c0.9,0,4.1-0.2,6.3-2.9c0.8-1.1,1.3-2.2,1.8-3.3c0.6-1.5,1.3-3,2.7-4.2c0.5-0.4,0.9-0.7,1.3-1.1l0.1-0.1c1.7-1.5,3.4-2.9,5.5-2.9c0.3,0,0.5,0,0.8,0.1c0.4,0.1,0.7,0.1,1.1,0.2c1,0.2,2.2,0.4,3.3,0.4c2.2,0,3.3-0.9,3.8-2.9c0.6-2.8,1.4-4.1,2.1-5.1c0.4-0.6,0.7-1.2,0.9-1.9c0.4-1.5,0.7-4.7,0.9-5.9l0.1-1.3l1.2,0.5c1.8,0.7,3.6,1.8,5.1,3.1c1.7,1.4,5,3.1,7.8,4.5c2.1,1,3.8,1.9,4.7,2.5c2.1,1.6,4.1,4.8,5.1,8.1c0.6,2.1,2.6,2.8,5,3.7c1.5,0.6,3,1.2,4.4,2.1c2.6,1.8,4.3,2,5.8,2c0.3,0,0.7,0,1,0c0.3,0,0.7,0,1.1,0c2.3,0,6.3-0.9,8.9-2.5c2.6-1.6,7-5.1,8.4-7.9c0.3-0.6,1-1.1,1.9-1.3c0.8-0.2,1.8-0.3,2.9-0.3c3.7,0,8.4,1.1,10,2.1c1.5,0.9,6,1.9,9.5,2.7c2.3,0.5,4.3,0.9,5.4,1.3c2.1,0.7,5.5,1.7,7.3,2.2l1.5,0.4l-1.1,1.2c-1,1.1-2.3,2.5-3.3,3.1c-0.6,0.4-1.2,1.1-1.9,1.8c-0.9,1-2.1,2.3-3.6,3.2c-0.9,0.5-2,1.5-3.3,2.6c-2.5,2.2-5.7,4.8-9.3,6.5c-5.4,2.4-10.9,8.4-11.9,10.4c-0.9,1.8-4.2,2.5-7.1,2.5c-1.3,0-2.5-0.1-3.7-0.4c-2.8-0.6-4.7-2.3-6.3-3.6c-1-0.8-1.9-1.6-2.8-2c-2.5-1-5-2-12.5-6c-1.3-0.7-2.3-1-3.1-1c-0.6,0-0.8,0.2-1,0.4c-1.2,1.2,0.1,5.1,0.9,6.9c1.1,2.1,0.5,5.3-1.5,7.8c-2.2,2.7-0.5,6.6,0,7.7c1,2,3.5,5,5.5,6.9c2.1,2.1,2.1,5.2,2.1,7.7c0,2.2-3.9,6.8-5.1,8.1l-0.6,0.7L502.2,366.1z"
}, {
  id: "b30",
  parentId: "a1",
  name: "yazd",
  persianName: "یزد",
  persianNickName: "یزد",
  ltrRotate: 0,
  ltrX: 645,
  ltrY: 570,
  d: "M632.8,710.7L632.8,710.7c-0.1-0.1-3.4-4.3-3.4-6.8c0-2.5-1.2-7.9-2.9-9.9c-1.3-1.6-4.7-4.4-6.6-5.7l-0.1-0.1l-0.1-0.2c-0.8-1.2-4.5-7.2-2.9-8.8c1-1,1.7-4.8,1.9-7.9c-0.1-2-0.5-11.2-0.5-14c0-3-0.5-5.4-2.9-7.3c-0.7-0.5-1.2-1-1.8-1.6c-1.5-1.3-2.7-2.4-4-2.4c-1.5,0-10.3-0.5-17.5-1l-0.7,0l-0.3-0.4c-2.3-3.1-5.6-6.9-7.7-7.6c-3-1-23.5-12.5-24.4-12.9l-0.2-0.1l-9.2-11.2l0.6-0.6c1-1.1,4.5-4.7,6.6-5.6c1.2-0.5,2.1-1.6,2.4-2.9c0.2-1.4-0.4-2.9-1.9-4.2c-2.5-2.1-4.7-5-5.9-6.6l-0.9-1.2l1.5-0.3c0.9-0.2,1.7-0.4,2.3-0.8c2.8-1.4,6.2-1.7,8.5-1.7c1.5,0,2.7,0.1,3,0.2l6.8-7.7l-10.9-12.9l0-0.4c0.7-6.3,1.5-14.3,1.5-15.7c0-1,0.1-6.9,0.3-12l0-0.9c0.1-5.2,0.2-10.2,0.2-11.1c0-1.1-0.7-3.7-1.8-6.8l-0.3-0.8l0.7-0.4c2.6-1.6,13.8-8.4,16-9.7c2.6-1.5,7.6-1.5,11.6-1.5c2.2,0,7.7-0.2,12.1-0.3c3.9-0.1,8-0.2,9.4-0.2c2.8,0,5.8-2.9,5.8-5.8c0-2.8,2.8-3.6,5.9-4.4c0.4-0.1,0.9-0.2,1.3-0.4c1.1-0.3,1.8-0.6,2.5-0.8c1.4-0.5,2.5-0.9,5.6-1.2c4.2-0.5,7.3-4.2,7.3-7.3c0-3,2.4-7.3,6.3-7.3h17c1.5,0,2.4-0.6,3.9-1.6c0.4-0.3,0.9-0.6,1.5-0.9c0.9-0.5,1.6-1.2,2.3-1.9c1.2-1.1,2.3-2.2,3.8-2.2c0.2,0,0.4,0,0.6,0.1c0.4,0.1,0.8,0.1,1.4,0.1c2.5,0,5.8-0.7,6.4-0.9c0.7-0.5,7.7-5.8,9.5-6.5c1-0.4,3-2.7,5.1-5.8l0.3-0.4h6.3c0.6,0,1.5-0.1,2.4-0.6l0.8-0.5l11.2,16.1l0,0.1c0.1,0.3,3.7,7,4,9.2c0.2,1.4,4.3,8.1,8.3,14c1.2,0.3,14.2,4,17,4.3c3,0.4,8.6,5.6,10,7.7c0.3,0.5,0.9,1.6,1.7,2.9c3,5.1,7.9,13.5,10.9,16c3.5,2.8,8.7,11.7,10.2,14.3l0.4,0.7l-0.5,0.5c-0.5,0.5-1.3,1.6-1.6,3.3c-0.4,2.4-0.4,7.8-0.4,8.2l0,0.1l0,0.1c-0.2,1.7-0.8,6.6-0.8,8.4c0,0.2,0,0.4,0,0.7c0,2.2,0.1,5.5-2.7,6.7c-0.6,0.2-1.2,0.5-1.9,0.8l-0.2,0.1c-2.7,1.1-5.7,2.3-6.6,3.3c-1.2,1.2-5.9,3.2-6.4,3.4l-3.4,1.7l-0.5-0.5c-0.6-0.6-2.2-2.1-4.1-2.1c-2.5,0-7.3,1.6-7.3,4.8c0,1.8-0.8,2.8-1.7,3.9c-0.8,1-1.7,2.1-2.1,4.1c-0.8,4.2-12.8,10.9-17.8,12.8c-4.6,1.7-11.3,3.8-11.4,3.8c0,0,0,0,0,0c0,0-0.7,0.3-1.7,0.7c-4.1,1.6-13.8,5.4-15.4,6c-2,0.8-13.9,4.2-15.3,4.6l-0.3,0.1l-0.3-0.1c-1.1-0.5-6.8-2.8-10-2.8c-0.2,0-0.4,0-0.6,0c-3.3,0.4-7.4,1.6-8.8,2.1c-1.1,0.4-3.7,1.4-4.4,1.6l0.8,33.5l-0.4,0.3c-1.7,1.2-7.5,5.4-9.4,6.5c-1.3,0.8-2.6,1.6-2.7,2.5c0,0.2-0.1,0.8,1.1,1.7c1.2,1,2.7,3.1,4.3,5.1c1.7,2.2,3.6,4.7,4.4,4.9c1.6,0.4,2.6,1.8,3.1,4.4c0.4,2.2,1.3,23.4,1.3,25.2c0,0.9,1.1,5.3,2.7,11.3l0.4,1.4l-1.5-0.1c-1.8-0.2-3.8-0.3-5.3-0.3c-1.5,0-2.2,0.1-2.4,0.2c-1.5,0.4-10.4,1.4-12.1,1.6l-0.6,0.1L632.8,710.7z"
}, {
  id: "b31",
  parentId: "a1",
  name: "zanjan",
  persianName: "زنجان",
  persianNickName: "زنجان",
  ltrRotate: 0,
  ltrX: 275,
  ltrY: 250,
  d: "M311.8,315.4c-1.1,0-2.2-0.5-3.1-1.4c-0.7-0.7-1.5-1-2.4-1c-0.9,0-1.8,0.3-2.7,0.6c-0.9,0.3-1.8,0.5-2.6,0.5c-1.2,0-2.2-0.7-3.3-1.6c-1.3-1-2.8-2.2-5.3-2.4c-3.9-0.4-7.1-2-7.9-2.4l-0.2-0.1l-0.1-0.2c-0.4-0.5-3.5-5-4.4-6.4c-1.1-1.6-4.1-1.9-5.8-1.9c-2.8,0-3.3-2.4-3.7-4.7c-0.4-1.8-0.7-1.8-2.1-1.8c-0.2,0-0.4,0-0.7,0c-0.5,0-0.9,0-1.5,0c-0.7,0-1.3-0.2-1.7-0.7c-1-1.1-0.7-3.3-0.3-5.6c0.1-0.6,0.2-1.1,0.2-1.4c0-1.5,0.4-3.2,3.7-4.2c0.5-0.2,0.9-0.5,1.1-1c0.6-1.4-0.2-3.9-0.7-5.1l-0.1-0.1c-0.3-0.4-0.8-2.1-0.6-2.9c0.2-0.6,0.1-1.6,0.1-2.2c0-0.1,0-0.3,0-0.3c0-1.2,0-1.4-0.1-1.4c0-0.1-0.1-0.3-0.2-0.6c-0.3-0.8-0.7-1.6-0.8-2.1c-0.2-0.7-0.7-1.7-1-1.9c-0.2,0-1.8-0.3-4.6-0.3c-2.8,0-6.2-0.8-10.1-2.5c-0.8-0.3-1.7-0.8-2.7-1.4c-2.2-1.2-4.5-2.4-6.1-2.4c-0.3,0-0.6,0-0.8,0.1c-0.5,0.2-0.8,0.5-1,1c-0.4,1-1.1,1.7-2,2c-0.4,0.1-0.9,0.2-1.3,0.2l0,0c-1,0-1.8-0.3-2.3-0.5l-0.6-0.3l0-0.7c0-1.2-0.1-2.5-0.3-3.4c-0.5-2.5-3-11.4-4-14c-0.8-2.1-2.8-8-3.6-10.5l-0.1-0.3l0.1-0.3c0.5-1.4,3-8.6,9.5-8.9c5.3-0.3,6.7-2.5,7.7-4.1c0.3-0.5,0.5-0.9,0.8-1.2c1.4-1.4,3.1-2.4,5.1-3.1c1.9-0.6,7.6-3.3,8.6-4.3c0.5-0.5,3.4-2.8,6.2-2.8c0.9,0,1.8,0.2,2.5,0.7c2.2,1.5,4.4,2.2,6.5,2.2c0.7,0,1.4-0.1,2-0.2c2.6-0.7,4.9-3.3,5.5-4.2c0.7-1.1,2.9-1.8,4.1-2.1c0.9-0.2,3.6-1.6,5.4-2.5l-1.7-3.2l5.3,3.4c0.5-0.1,1-0.1,1.6-0.1c1.3,0,1.6,0.2,1.8,0.3l0.2,0.1l0.1,0.2c0.4,0.6,0.8,1.5,1,1.8l3,0.8l0.2,0.3c0.3,0.5,0.9,1.4,0.9,2.1c0,0.6,0.5,1.9,1.8,2.3c0.3,0.1,0.6,0.2,0.9,0.3c0.5,0.2,1,0.3,1.4,0.3c0.4,0,0.6-0.1,0.9-0.4c1.2-1.2,2.9-2.7,4.2-2.7c0.2,0,0.4,0,0.5,0.1c0.5,0.2,1.5,0.3,2.4,0.3c1.4,0.1,2.8,0.2,3.6,0.7c0.1,0.1,0.5,0.3,1.5,0.3c1.5,0,3.4-0.5,4.3-1.1l0.7-0.4l0.6,0.6c0.4,0.5,0.8,0.7,0.9,0.8l0.1,0l0.1,0.1c2.6,2.6,11.2,11.2,12.5,13c1.5,1.9,5.2,10.7,5.5,11.5c0.3,0.3,2.8,2.8,5,5.1l1.6,1.7l-3.9,0c-0.3,0-0.9,0.1-1.5,0.1c-0.5,0-0.9,0-1.2-0.1c-1.1-0.2-2.1-0.8-2.6-1.7c-0.5-0.8-1.9-1-3.2-1.2c-1.1-0.1-3.4-1-4-1.3l-2.6,3.6l0,0.1c-0.2,0.7-2,6-3,7.5c-0.9,1.4,0.1,5.4,1.5,8.3c1.4,2.7,4.8,3.3,7.8,3.8l0.5,0.1c2.2,0.4,4.1,1.2,5.9,2.1c0.7,0.3,1.5,0.7,2.2,1c2,0.8,3.4,2.3,4.1,4.7l0.3,0.8c0.9,2.5,1.7,5.2,1.7,6.8c0,1.4-1,4.9-2.2,8.7l0,0.1c-0.4,1.2-0.7,2.2-0.8,2.7c-0.5,2-4.4,4.2-8.7,4.7c-2.8,0.3-3.5,1.9-4.3,3.6c-0.3,0.6-0.6,1.3-1,1.9c-0.5,0.7-1.2,1-2,1.1c-0.1,0-0.3,0-0.4,0c-1.5,0-3.4-0.9-5.5-2.6c-2.4-2-3.8-2.7-4.3-2.9l-7.9,7.9c-1.1,1.1-1.7,3.6-1.9,7.6l0,0.2l0,0.1l0,0l0,0.2c0,0.8,0,1.5,0,2.3c0,1.1,0.6,1.9,1.2,2.6c0.7,0.9,1.4,1.8,0.8,3c-0.6,1.3-1.9,2.2-3.2,2.4C312.2,315.4,312,315.4,311.8,315.4z"
}];

var iransSeasProperties = [{
  id: "b47",
  parentId: "a1",
  name: "khazar",
  persianName: "دریای خزر",
  persianNickName: "دریای خزر",
  ltrRotate: 0,
  ltrX: 445,
  ltrY: 130,
  d: "M361.4,0l-1,0.6l-0.6,0.8l-0.1,1.5l0.3,1.8v0.8l-3.1,1.1l-0.6,1l0.1,1.4l0.8,1.4l0.5,0.6l0.9,0.6l0.4,0.5l0.3,0.7l-0.4,0.4l-0.5,0.4l-1.1,0.8l-0.4,0.2l-0.5,0.3l-0.4,0.7l-0.2,0.9l-0.1,0.6l0.3,1.4l0.7,1.4l0.2,0.8l-0.3,0.8l-0.5,0.6l-0.4,0.3l-0.4,0.4l-0.1,0.7l0.1,0.3l0.2,0.4l0.2,0.4l-0.1,0.5l-0.2,0.3l-1,0.6l-0.3,1v0.5l0.3,0.4l-0.2,0.9l0.3,1l1.3,1.7l-0.1,0.6l-0.8,0.5l-1.5,0.8l-2.7,3l-1.1,1.8v1.1l-0.7,1.2l-0.6,1.5l-0.4,1.6l-0.3,1.4l0.1,1.9l0.6,1.2l5.4,4.6l0.7,0.8l0.5,0.9l-0.1,0.3l-0.2,0.2l-0.4,2.3l0.1,0.7l0.5,0.8l-0.7-0.3l-0.6-0.5l-0.4-0.5l-0.3-0.6h-0.4l0.2,1.1l0.5,1.1l0.8,1l0.9,0.6v0.5l-1.3-0.3l-0.9-0.9l-0.7-0.9l-3-1.9l-2,0.7l-1.5,1.8l-0.6,2.2l0.1,7.6l-0.5,2.1l-0.8,2.2l-0.3,1.1l-0.2,2.4l-0.3,1.5l-0.5,1.2l-4.4,2.9l-2.3,0.8l-1.6-1.2l0.2-0.8l-0.1-0.6l0.1-0.4l0.6-0.6l2.6-0.4l0.9-0.5l0.8-1l0.5-1.4v-1.4l-0.7-1.3l-1.1-0.5l-2.8-0.1v-0.6l-0.4-2.9l-0.2-0.8l-1-0.8l-1.1-0.2l-2.6,0.1l-0.6,0.2l-0.4,0.5l-0.2,0.7l-0.5,1V71v0.7l-0.2,0.6l-0.2,0.1h-0.3l-0.2,0.1l-0.1,3.2l0.2,1.7l1,1.5l-0.3,1.7l-1.5,4.9l-1.4,3l-1.8,2l-2.1-0.5v2.4l0.2,1.2l0.2,1l1.4,3.3l0.7,22.3l0.2,6l-0.7,2.1l0.4,1.4l0.1,3.7l1.1,2.5l0.9,8.5l2.4,8l-0.5,1.4v1.5l0.2,1.5l0.5,1.1l2,3.1v0.7l-0.1,0.7l-0.1,0.5l0.6,2.7l1.2,2.6l3,4.1l3.9,3.9l4.3,2.8l9.4,4.6l4.4,1.4l22.5,2.9l2.4-0.4l2-0.7l1.9-0.3l2.1,1l-0.6,0.1l-0.6-0.2l-0.3-0.1l-0.5,0.6l4.9,1.8l7.6,1.6l2.7,1l1.9,1.7l-0.2,2.5l0.5,0.9l0.7,2.5l0.6,1l0.8,1.3l1.4,3.7l1.8,2.7l2,1.9l4.2,3l2.9,3.3l0.9,0.5l1.1,0.3l6.5,4.2l1.2,0.2l0.8,0.4l1.8,1.7l0.8,0.8l9.3,4.7l8.4,5.7l4.9,2.1l16.4,3.1l10.4,2.8l10.8,1.9l10.4,2.8l10.9-1.3l9.6-3.4l10.1-2.3l10.4-1.9l10-1.9l10-2.9l9.7-2.8l19.4-4.1l2.6-0.4l23.1-1.3l4.2-0.9l2.8-2.3l-0.1,2.6l-3.3,1.1l-4.2,0.5l-2.7,0.8l-0.7,0.3l-0.8-0.1l-1.6-0.4l-0.9,0.1l-1.6,0.6l-0.9,0.2l-3.4-0.5h-3l0.4,0.8l0.8,0.3l2-0.1l-1.2,0.3l-0.5,0.1l1.4,1.8l2.4,1l9.1,0.8l0.9,0.4l1,0.4l7.4-1.9l0.7-0.6l0.4-1.1v-7.2l-0.3-1.1l-0.9-0.5l-1.1-0.4l0.2-1l1.3-2.4l-1.4-2l-0.9-2.6l-1.3-5.8l-1.8-4.5l-0.3-1l-0.5-5.9l-0.8-8.6l-0.6-2.8l-1.1-2.7l-0.4-1.4l-0.2-3l-2.1-9.2l-1.1-19.9l0.2-1.1l0.8-2.3l0.6-3.4l1.5-5.2l-0.3-1.9l0.7-2.2l0.1-2.9l-0.3-5.1l-0.1-0.5l-0.5-1l-0.3-0.6l-0.1-0.7l-0.1-1.4l-0.9-4.2l-0.1-1.5l0.5-5.6l0.7-2.8l0.9-2.3l2.8-4l1-2.5l-0.6-2.1l0.9-0.6l0.4-1.3l0.3-1.4l0.6-1.1l0.6-1l0.7-1.3l0.3-1l-0.5,0.2l-0.1-1.5l-0.8-0.7l-2.1-0.7v-0.1l-0.2-0.6l-0.1-0.2l-0.3-0.1l-0.7-0.3h-0.2l-0.3-0.5l-0.3-0.5l-0.2-0.7l-0.1-0.7l-0.6-1.4l-0.7-0.5h-2.3l-1.4-0.4l-0.5-0.1l-0.6,0.3l-0.3,0.4l-0.3,0.1l-0.6-0.5l-0.5-1.1l-1.2-3.2l-0.3-0.7l-0.6,0.5L607,75l0.5,1.1l0.4,0.6v0.5l-0.9-0.5l-0.8-1l-0.4-1.3l0.6-1.9l-0.5-1.3l0.1-0.6l0.3-0.5l1.6-1l-1.7-0.1v-1.5l1.3-3.1l-1.2,0.6l-1.6,1.1l-1,1.1l0.9,0.5l0.5,7.6l-0.7-1l-1.4-1.8l-0.7-1l-0.2-1.2l-0.1-1.4l-0.4-1.1l-1.3-0.1l0.3-0.8l0.2-1.2l-0.1-0.9l-0.6-0.4l-0.3,0.4l-0.9,2.2l-0.6,0.7l-0.2-1.6l0.3-2l1.1-4l-1.6,1.4l1-2.3l0.2-1l-0.4,0.2l-1.2,0.3l0.7-1.5l-0.2-0.5l-0.7,0.3l-1,1.2l-0.4-0.5l-0.7,0.4l-2.5,0.1l-1.1,0.9h-0.5v-1.4h-0.4l-0.4,0.7l-0.7,0.7l-0.8,0.5h-0.9l0.3-0.4l0.5-1.5h-0.4l-0.8,0.1l-0.4-0.1l-0.1,0.1l-0.5,0.4h-0.2l-0.2-0.1l-0.4-0.7l-0.2-0.1l-0.8,0.3l-1.5,0.6h-0.9v-0.5l0.3-0.5l-0.1-0.2l-0.5-0.1l-0.7-0.1l-0.7-0.1l-0.9-0.6l-0.6-0.2h-1.2l-2.8,0.8l-1.2,0.6l2.1,1.2l0.7,0.2l-1.1,1.6l-0.4,0.9l-0.1,1.1l0.1,1.1l0.7,2.9l-0.2,1.7l-0.5,0.8l-0.6-0.1l-1.5-9.8l-0.4-0.9l-2.4-3.4l-0.2-1.2l0.5-1.3l0.6-0.7l1.7-1.4l0.2-0.7l0.2-0.9l0.3-0.8l1.2-0.8l0.7-1.3l2.2-5.4l1.5-3l2.1-2l2.2,0.5l-1.3,0.6l-0.9,0.7l-1.7,2.2l-0.2,0.5l-0.5,2.1l-0.2,0.2l-1.2,1.2l0.3,1.7l2.2,0.3l6.4-1.2l3.7,0.2l1.2,0.3l0.7,0.9l0.5,1.1l0.6,0.9l0.8,0.6l1,0.3l2.4,0.1l1,0.5h0.6l0.2-0.7v-0.7l-0.2-0.5l-0.4-0.4l-0.6-0.1l0.8-1.7l0.7,0.2l0.8,1.1l0.9,0.9h1.1l1.7-1.6l1.2-0.3l0.6,0.2l1.3,0.7h0.5l0.7-0.6l-0.2-0.7l-0.6-0.6l-0.6-0.5l-1.3-0.4l-2.5-0.6l-1.1-0.8l1-0.3l0.5-0.5l0.1-0.8l-0.6-1l-0.7-0.7l-0.8-0.2l-2.8,0.3l-0.2-0.4l-0.1-1.4l-0.2-0.7l-0.4-0.8l-0.7-0.7l-0.7-0.4l0.4,2.3v1h-0.4l-2.1-3.1l-1.5-1.3l-1.6-0.3l0.2,0.3l0.6,1.6l-0.4-0.3l-0.9-0.4l-0.3-0.3V35l1.1,1.3l0.1,1.1l-2-1.2l-0.2-2.5l1-5.3l-0.7,0.4l-0.8,0.1l-0.7-0.2l-0.6-0.3v-0.5l1.9-0.8l3.1-4l1.8-1.8l-0.3-0.4l-0.3-0.7l-0.2-0.3l0.5-0.3l0.5-0.1l1.2-0.1l0.8-0.2v-0.6l-0.3-0.4l-0.3-0.2l0.6-0.8l1-0.8l0.8-0.9l0.4-1.3l-0.3,0.2h-0.1l-0.2,0.1l-0.2,0.2l-1-0.9l-0.8-0.2l-2.2,0.1l-1-0.3l-1.3-1.1l-0.9-0.5l-1-0.2l-1.1-0.1l-1,0.3l-0.9,0.5l-2.5,2.6l-0.9,0.3l-0.3,0.1l-0.9,0.7l-0.5,0.1l-0.4-0.1l-1.1-0.7l-0.5-0.1l-0.6-0.3l-3.8-2.7l-1,0.3l-0.9,0.8l-0.8,0.4l-4.3,0.5l0.4-0.6l0.3-0.5l0.4-0.4l0.6-0.4l-4.1,1.2l-2.2,0.3l-1.8-0.5l-0.9-2.1l-0.9-0.7l-1,0.9v0.7l0.4,0.9l1,1.5l0.2,0.8l0.4,3.9l0.4,0.6l1.6,2l0.6,0.4l2.2,3.8l1.9,1.6l0.5,0.3v0.5l-2.8-1.4l0.8,0.5l1.6,1.9l-0.4,0.4l-1.8-1.7l-0.8-0.9l-1.7-3.7l-0.8-0.9l-2.1-0.8l-0.6-1.1l-0.4-1.5l-0.4-2.7l-0.5-0.7l-5.6-4.1l-2-1.9l-0.9-1.5l0.4-3l0.5-1.7l0.5-1l0.3-1.2l-0.6-1.3"
}, {
  id: "b48",
  parentId: "a1",
  name: "khalijefars",
  persianName: "خلیج فارس",
  persianNickName: "خلیج فارس",
  ltrRotate: 0,
  ltrX: 530,
  ltrY: 970,
  d: "M269.3,730.4l-1.1,1.9l-1.6,1.5l-3.5,2.3l-1.5,1.6l-2.4,3.4l-1.1,1.1l-2.7,2.1l-0.7,0.3l-0.1,0.1l0.4,0.4l0.7,0.3l0.6,0.1l2.3-0.5l2.2-0.1l0.8-0.2l1-0.6l0.1,0.8l-0.7,1.6l-0.3,1.2l0.4,0.9l0.8,0.3l1.9-0.1l1.5-0.5l3.7-2.7l1.2-1.2l0.5-0.1l0.7,0.7l1,1.5l0.9,0.8l0.6,0.2l2.5-0.1l0.2,0.1l-0.3,3.9l0.1,2.2l1.8,4.8v1.1l-0.1,1.1l3,10l1,2.3l2.9,4.6l0.9,0.8l2.3,0.8l0.1,1l-0.2,1.4l-0.1,1.4l0.5,1.3l1.6,2.4l0.4,0.8l0.6,1l1.3,0.6l2.5,0.5l-0.6,1.1l-0.3,1.2l0.1,1.3l0.4,1.1l-0.9-0.6l-0.3-0.3l-0.1,0.6v0.3l0.3,0.3l0.6,0.3l-0.5,0.5l-0.3,0.2l-0.2-0.1l-0.2-0.2h-0.4l-0.1,1.4l0.5,0.4l0.8-0.4l0.8-0.9l0.1,0.7l0.3,3.3l0.2,0.9l0.4,0.9l0.9,1.3l0.7,0.7l1.4,1.6l0.8,0.5l1.5,0.7l0.2,0.5l0.5,3.1v2.3l-0.5,1.5l-1.3-0.5l-0.3,0.5l-0.1,0.2v0.2l1.1,0.1l1-0.2l0.7-0.7l0.4-1l0.7,0.4l-0.1,0.6l-0.6,1.3l-0.4,1.8v0.8l0.3,1.7l0.7,1.3l4.9,5.7l0.3,0.8l-0.8,1.3l-0.5,1.3v1.4l0.3,1.4l0.6,1.1l1.9,2.7l0.3,0.7v0.8l-0.1,0.3l0.9,0.6l2,0.9l0.6,0.1l2-0.1l0.6,0.2l1.1,0.7l0.7,0.1l0.3,0.2l-0.1,0.4l-0.1,0.5l-0.3,0.3l-0.3,0.2H318l-0.5-0.2l-1,0.5l-0.2,0.5v1l0.6,0.9l1.2,1.2l1.3,1.1l1.1,0.5v0.3l1.3,2.1l2.4,2.5l0.3,0.6l-0.5,1.4l-0.1,0.9v0.8l0.2,0.4l-0.1,0.5l-0.5,1.1l-0.8,1.1l-0.8,0.6l0.5-0.8v-0.6l-0.1-1.7l0.2-0.9l0.3-0.6l0.2-0.6l-0.3-0.9l-0.8,0.9l-1,2.6l-1,0.7l1.1-3l0.1-0.8l-0.2-1.3l-0.5,0.1l-0.5,1l-1.1,4.8l-0.1,1.1l-0.1,0.2l-0.2,0.4l0.1,0.4h0.6l0.4-0.4l0.4-1.1l0.4-0.5v3.1l0.2,0.8l0.6-0.1l0.5-0.6l0.3-0.8l0.4,0.8l0.1,0.9l-0.1,1.2l0.7,0.3l0.6-0.4l0.4-0.6l0.3-0.7l0.1,1.2l-0.2,0.4l-0.3,0.3l0.3,0.6v0.4l-0.4,0.3h-0.7l0.6,1.5l0.2,0.4l-1.4-0.7h-0.6l-0.4,0.7l1.2,0.6l1.1-0.1l0.8-0.6l0.5-1.3h0.4l0.4,1l-0.7,0.8l-0.2,1.3l0.3,1.1l1,0.1l0.5-0.5l-0.3-0.5l-0.4-0.5l-0.2-0.5l0.5-0.6l0.6-0.3l1.4-0.4l1.1-0.1l0.8,0.4l2.1,2l2.1,1.2l0.6,0.8l-1.1,0.9l0.8,0.4l0.7-0.1l0.4-0.5l-0.3-0.8l1,0.5l1,0.3l2.2,0.2l0.5-0.2l1-0.6l0.5-0.2l0.6,0.1l1.2,0.4h0.6l1.2,0.4l0.9,0.9l1.3,2l0.5,0.4l0.4,0.2l0.4,0.3l0.3,0.5l0.2,0.6l0.1,1.2l0.2,0.6h-0.8l-0.4-0.3l-0.2-0.7l0.1-0.9H348l-1.2,1.6l-3.2-0.4l-1.2,1.2H342l-0.4-1.2h-1l-2.2,1.2l0.4,0.3l1.3,0.4l0.7,0.3l0.5,0.4l0.4,0.3l0.4,0.4l0.7,0.3l0.4,0.5l0.3,0.3l0.3-0.2l1-1v-0.1l0.3-0.3l0.1-0.4l0.2-0.3l0.4,0.3l0.4,0.4l0.6,0.3l-0.4,0.9l-0.6,0.5l-0.5,0.3l-0.5,0.6l-0.2,0.8v1.8l-0.2,0.8l0.7-0.2l0.6-0.4l0.7-0.5l0.6-0.6l0.7-0.2l0.8,0.2l1.2,0.7l-0.5,1.4l0.2,1.3l0.4,1.3l0.2,1.4l-0.1,3l0.3,1.2l1-0.1v1.3l0.4,0.4l0.6-0.1l0.6-0.7l-0.3-1l0.6-0.7h0.9l0.8,0.8l0.4-0.5l0.3,0.8l-0.2,0.7l-0.3,0.7l-0.2,0.9l-0.2,0.5l-0.5,0.2l-0.6,0.1l-0.7-0.1l0.5,0.8l1.4,0.3l0.5,0.8l0.6-0.4l0.3-0.6l0.7-1.4l0.1,0.3v0.1h0.1l0.2,0.1l-0.6,1.2l0.5,0.2l1.5-0.5l0.9,0.2l1.6,0.7l1,0.1l-1.6-1.8l-0.5-1.1l0.9-0.9l0.7-0.1l0.5,0.4l0.6,0.5l0.5,0.2l0.5-0.3l1.1-1.2l-0.2,1.1l-0.5,1.7l-0.1,1l0.4,1.6l0.3,0.9l0.3,0.3l1.1,0.6l1.1,1.3l3.4,5.6l1.7,2.2l0.5,0.5l1.7,0.7l0.5,0.5l0.9,0.9l0.6,0.5l3.6,1.8l2.3,1.8l1.3,0.1l1.3-0.1l1.5,0.2l1.8,1.1l1.7,1.8l2.9,4.2l1,1.9l4.3,3.3l1,1.1l0.2,1.8l-2.7-2.5l-1.4-1l-3.2-0.4l-0.8-0.3l-0.6-0.8l-0.4-2.5l-0.6,0.4l-0.5,1.2l-0.3,1.1v0.9v0.8l0.2,0.8l0.4,0.6l0.6,0.7l0.2,0.3l-0.3,4.2l0.1,1.2l1.6,5.3l0.6,1.1l1,1l1.1,0.7l5,1.8l1.7,1.6l1,2.4l0.5,3.1l-0.1,7.6l-0.2,1.6l-0.6,1.4l-1.1,0.8l-0.1-1.1l-0.4-0.4l-0.6,0.3l-0.6,0.7l0.4,1.8l-0.1,2.6l-0.5,2.8l-0.5,1.8l-0.9-0.7l-0.3-1v-1.1l-0.1-1l-0.4-0.8l-0.5-0.6l-0.6-0.4l-0.4-0.5l-0.4-0.3h-0.2l-0.2-0.2l-0.1-1.9l-0.1-0.4l-0.3-0.6l-0.4-0.7l-0.7-0.7l-0.8-0.5l-0.7,0.3l-1.5,3.1l-0.5,0.5l-0.6,0.4l0.3,0.9l0.6,0.9l0.3,0.3l0.2,0.6l0.5,0.9l0.1,0.7l-0.2,0.2l-0.4,0.1l-0.4,0.3l-0.2,0.5l0.1,1.1l0.3,0.9v1l-0.4,1.1l1,0.4l0.8-0.6l0.4-1l-0.2-1.2l0.6,0.2l0.4,0.4l0.6,0.9l0.3,0.1l0.3-0.1l0.2,0.1v0.5v0.5l0.1,0.2l0.2,0.1h0.3l1.5,0.3l0.6,1l0.3,1.2l0.7,1.2v0.5l-1.2,1.3l0.6,3.3l1.4,3.5l1.2,2.3l3.5,4.5l1.5,2.7l0.6,3.3h-0.4l-1-3.3l-0.4-0.6l-0.7-0.1l-0.9-0.5l-0.7-0.5l-0.8-1.2l-0.9-0.7l-0.8-0.2l-0.2,1.4l0.4,1l1.5,1.1l0.5,0.7l0.3-0.7l0.1-0.3h0.4l2.2,5l6.7,9.2l1.5,1.4l-0.2-0.9l-0.4-1.1l-0.1-0.8l0.5-0.4l0.6-0.3l0.3,0.1l0.2,1.5l0.3,0.4l0.3,0.2l0.1,0.2l0.5,0.9l1.1,0.6l2,0.6l0.5,0.7l1.1,3.1l-0.4,0.5l0.7,1l0.8,1.9l0.6,2l0.3,1.5v0.8l-0.3,1.6l-0.1,0.9l0.1,0.9l0.3,0.6l0.3,0.5l0.3,1.1l0.8,1.7l0.2,1.1l-0.4,2.8l0.5,2.8l0.5,1.6l0.6,0.8l0.5-1.3l1.5,1.3l1.6,2.2l0.6,1.1l1,1.1l1.2,4.5l1.4,1.1l1.2,1.2l0.5,2.6l0.1,4.2l0.3,0.8l0.5,1.3l0.6,1.1l0.6,0.7l0.9-0.1l1.3-1.3l1.1-0.1l1.5-1.5l0.4-1.8l-0.5-6.6l-0.5-1.7l-2.5-5l-0.2-1.1l0.6-1.9l0.2-1.3l-0.1-1.3l-0.3-0.5l-1.6-1l-0.4-2.4l-0.1-2.5l-0.6-1.7l0.5-1.2l-0.1-1.5l-0.3-1.5l-0.1-1.5l0.5-3.8v-1.4l-0.9-5.2l0.7-3l0.1-1.3l-0.8-0.9l1.6-2.2l1.3,1.5l1.2,2.3l1.6,0.3l-0.9-2.8l-0.3-1.2v-1.2l0.1-0.8l0.2-0.8v-0.9l-0.3-0.8l-0.5-0.4l-1.3-0.2l-0.7-0.4l0.7-0.8l0.8-0.3l0.8-0.1l0.8-0.4l0.2-0.4l0.3-1.1l0.3-0.2l0.4,0.1l0.3,0.7l0.5,0.1l0.3,0.6l-0.1,1.1l-0.4,1.9v1.4v0.5l0.5,1.4l0.3,0.3l0.4,0.4l0.6-0.2l0.1-0.1v-0.4l0.2-1.6v-1.7l0.3-0.7l0.7-0.7l0.4,0.2l0.5,0.5h0.8l0.3-0.5l0.9-2l0.4-0.8l-1.6,0.6l-1.5,0.3l-1.2-0.5l-0.9-1.8l-0.1-1l0.5-3.3l0.1-0.3l0.6-0.5l0.1-0.4l-0.1-0.3l-0.3-0.4v-0.3v-2l0.8,0.2l0.3-0.6l0.1-0.7l0.6-0.4l0.4,0.2l0.3,0.6l0.3,0.8v0.8l0.8-0.5l0.5-1l0.2-1.1l-0.3-1.2l-0.4,0.5l-0.8-1l0.1-1.5l1.5-3.9l0.2-1.3l0.2-3.2l0.5,0.4l0.2,0.2l0.1,0.4h0.4l1.3-4.1l1.2-1.8l1.7-0.8l0.9-0.2l2.4-1l0.5-0.4l0.3-1.1l1.4-1.5l0.3-1l1.1,0.4l1.2-0.4l2.1-1.4l4.7,2.7l0.9,1.1l0.1,1.3l-0.1,1.7v1.5l0.7,0.7l1.1,0.4l0.3,1.2l0.1,1.4l0.3,1.3l0.9,0.9l1.2,0.2l2.5-0.2l1.4,0.1l1.2,0.4l1,0.7l1,0.7l0.8,0.9l0.6,1l0.4,1.3l1,7.5v0.9l-0.2,0.8l-0.4,0.4l-0.4-0.3l-0.3-1l-0.5-0.2l-0.5,0.3l-0.4,0.7l-0.2,0.8l0.1,0.6l0.5,0.5h0.5l0.4-0.5l0.2-0.5l1,1.6l-0.8,1.6l-1.2,0.5l-0.2-1.8l-0.8,0.3l-2,1.1l0.8,0.4l0.9,0.6l0.7,0.7l0.4,0.7l-0.2,1.5l-0.8,0.6l-1,0.3l-0.8,0.4l-0.4-0.2l-0.4-0.2l0.1,3.6l-0.1,1.2l-0.3,0.6l-0.5,0.6l-0.4,0.7l0.2,0.6l2.1,4l0.4,1l0.1,1l-0.4,6.6l0.1,1.5l0.3,0.8l0.7,0.3l3.5,0.6l0.5,0.6l0.5,1.4l0.4,2.4l0.1,5.7l-0.6,7.1l0.3,0.9l-0.5,0.5l-0.9,4.2l-0.8,1.3l-2,2.5l-0.6,1.7l-0.5,0.2l-0.5,0.2l-0.4,0.3l-0.3,0.6l-1.6,6.6l-0.3,0.8l-0.7,0.5l-0.3,1.3l-0.6,3.3h189l-0.4-0.3l-0.3-0.7l-0.1-0.8l-0.3-0.9l0.3-0.5l-0.4-0.3l-0.5-0.5l0.2-1.1l0.5-0.7l2.3-1.7l0.3-0.4l0.3-0.7l0.3-0.4l1.8,0.9l0.1,0.1l0.9-0.2l0.8-0.6l0.3-0.9l-0.8-1.1l6.4-4l2.9-2.2l1.7-1.8l1.2-0.8l2.2-0.8l1-0.6l1.6-1l-0.3-1.5l1.9-0.4l0.3,0.2l4.4-5.5l5.9-8.2l0.3-1.1v-0.9l1.1-1.1l0.9,0.1l0.9,1.4l0.3,0.9l-0.2,1l-0.8,1.2l1.6-0.5l0.3-1.2l-0.4-1.6l-1.2-2.3l-0.1-0.6l0.3-0.6l1.7-2l0.6-0.2h0.8l-0.2-0.8v-0.9l0.4-0.7l0.6-0.4l0.6,0.5l1.2-1l1.9-2.8h0.3l0.3,0.8l0.3,0.1l0.4-0.5l0.2-0.9l0.4,0.5l0.8-2.6l0.6-1.1l0.6-0.6l-0.7-0.4l0.4-0.9l0.7-1l0.4-1.2l0.3-1.2l0.6-1.3l0.9-1.2l1-0.4l-0.5,1.1l-0.6,1l-0.4,0.8l0.4,0.9l0.9,0.4l1.1-0.2l1.3-0.4l1.2-0.2l0.4-0.6l0.9-2.7l0.5-1l1.6-1.8l0.9-0.7l2-0.9l1.5-2.2l0.7-0.6l0.5-0.1l0.7-0.2l0.7-0.4l0.3-0.4l0.3-0.2l1.7-0.5l2.1-1.8l3.2-4.3l1.5-1.5l-0.3,0.6l-0.4,1.4l-0.6,1.3l0.3,0.4l0.4,0.1l0.2-0.2l0.1-1.1l0.6-1.9l0.1-1.3l0.4-0.6l2.4-2.5l0.6-0.7l0.4-0.8l0.4-1l0.2-1.3h-0.4l-0.2,0.7l-0.3,0.5l-0.5,0.4l-0.5,0.3l1.5-2.8l1.2-2.9l1.1-4.4l0.2-0.6l0.3-0.7l0.6-2.4l3.8-6.6l1.5-3.1l0.5-0.6l1-0.5v0.3v1l0.7,1.1l-0.2,0.4l-0.3,1h0.5l0.5-0.7h1.6l0.3-0.5l0.3-0.2l0.8,0.3l0.7,0.8l0.2,1.2l0.4-0.8l0.4,0.1l0.5,0.3l0.7-0.1l1.6-1.2l0.6-0.2l1.8,0.6l0.4-0.1l0.1-0.6l-0.2-0.6l-0.5-0.5l-0.4-0.2l-1.2-0.1H762l-0.5,0.3l-0.3,0.5l-0.6,0.6l-0.7,0.4l-0.6-0.3l-0.1-0.7l0.5-2.9V959l1.7,1.4l0.8,0.3l0.3-1l-0.3-0.5l-0.6-0.7l-0.8-0.6l-0.7-0.3l0.2-0.6l0.3-0.1h0.4l0.3-0.3l0.8-0.9l0.3-0.8l-0.1-1.5l0.2-1h0.4l0.8,1.8l0.9-0.6l0.3-0.3l0.4,0.5l-0.3,0.5v0.2l0.1,0.2l0.2,0.5l0.6-0.5l0.3,0.2l0.3,0.4l0.4,0.4l1.4,0.4l0.7,0.1l0.7-0.1l-0.1-0.3l-0.2-0.8l-0.1-0.3l1.2-0.5l0.6,1.8l-0.1,0.7h-0.8l-1.5-0.1l-1,0.4l-1.7,1.7l-1,0.6h0.1l-0.1,0.4l-0.5,0.8l1.3,1.4l0.7,0.6l0.8,0.3l0.5-0.3l0.6-0.6l0.7-0.1l0.6,1l-1.1,2l-0.5,0.3l-0.4-1.4l-0.6,0.1l-0.6-0.1l0.2,0.7l0.1,0.4l-0.1,0.4l-0.2,0.4l0.7,0.8l0.9,0.6l0.8,0.7l0.4,1.3l-0.7-0.1l-0.6-0.1l-0.6-0.4l-0.5-0.4l-0.8,0.4l-0.7-0.3l-0.5-0.9v-1.1l-0.4,0.3l-0.9,0.4l-0.3,0.2v-0.7l0.1-0.6l0.3-0.4l0.4-0.2l-1.3-0.2l-1.5,0.9l-0.8,1.3l0.4,0.9l-0.3,0.7l-0.1,0.9l0.1,0.8l0.3,0.9l0.5-1.4l0.5-0.7l0.6-0.2l0.4,0.4v0.8l-0.1,0.9l-0.3,0.7l1.1,0.5l5.3-0.1l-0.5,0.9l-0.9,0.8l-1.8,1.2l-1.7,0.7l-0.5,0.6l0.2,1.1l1.4-0.8l0.9,0.7v1.3l-1.4,1l0.3,0.7l0.8,1.1l0.2,0.5l0.5,0.3l1.3,0.4l-0.4,0.3l-0.2,0.2l-0.2,0.9l-0.9-0.5l-0.9-0.3l-0.9,0.2l-0.5,0.6l0.9,1.7l-0.4,1.5l-1,1.4l-0.7,1.5l-0.1,0.5l0.1,1.7l-1.2,1.2l-0.9,1.8l-0.7,0.9l-0.8,0.6v-1.5l-0.8,1.5l-0.9,2.2l-0.4,2.5l0.4,2.3l0.3,0.9l1.3,0.7l1.3,0.6l1,0.2l0.5,0.8l1.3,4.7l-0.4,6.4l0.3,2.5l-0.1,0.5l-0.5,0.9l0.1,0.6l0.6,1.1l0.2,0.7l0.3,0.5l0.2,0.5l0.1,0.9l-0.1,0.8l-0.2,1.4l-0.2,2l-0.6,3l-0.2,10.5l1.2,5.5l1.3,5.6l3.8,8.4l0.6,0.7l0.4,1.6l0.4,2.9l0.9,1.8H1200v-47.8l-0.8-0.2l-0.6-0.1l-0.8-0.2l-0.8-0.3l-2.2-0.4l-2.3-0.3l-2.4,0.2l-3.8,0.6l-1.9,0.7l-1.1,0.6l-1,0.8l-1.6,1.9l-0.8,1.8l-0.6,0.5l-1-0.4l0.3,1.1l0.5,0.9l1.7,2.3l0.3,0.3l0.1,0.1v0.5l-0.2,0.5l-0.2,0.5l-0.3,0.3l-0.3,0.1l-1.9-0.4l-3.4-1.6l-2-0.3l-4,0.5l-1-0.2l-2.7-1.3l-3.9-1.1l-2-0.2l-1.8,0.4l-3.7,2.1l-1.3,0.3l-5-0.5l-10.1-2.4l-8.2-0.2l-7.6,0.7l-1.3,0.4l-0.8,0.8l0.2,1l1.3,0.6l-1.2,0.5l-1.5-0.5l-1.8,0.5l-1.6,1l-1.2,0.9l-0.6,0.7l-0.7,1l-0.4,1l0.2,1.1l0.6,0.4l1.9,0.3l0.7,0.2l-1.1,1l-2.1,0.1l-2.2-0.4l-1.4-0.7l0.1-0.4l0.3-0.2l0.2-0.1l0.1-0.2l0.6-0.3h0.5l0.4-0.1l0.1-0.8l0.1-1.5v-0.8l-0.3-0.5l-1.1-1.2l-1.2-0.9l-1.3-0.7l-1.4-0.3l-2.1,0.1l-2.8,0.5l-2.5,0.9l-1.4,1.3l-0.2,0.7l-0.2,0.9l0.1,0.9l0.5,0.4l1.5,2.1l-0.6,0.5l-1.3-0.1l-2.6-0.7l-5-0.4l-1.3,0.2l-2.4,1.3l-1.3,0.4l0.6,0.9l-0.2,0.6l-0.5,0.6l-0.6,2l-0.7-0.1l-1.4-0.8l-1,0.1l-1.5,0.7l-0.9,0.2l-0.7-0.2l-0.7-0.6l-0.2-0.8l0.6-0.7l-0.5-0.9l0.3-0.6l1-0.9l0.6-0.8l0.1-0.4l0.1-0.9l0.2-0.8l0.8-1.1l0.2-0.8l-0.1-1l-0.2-0.2l-0.3,0.2l-0.4,0.1l-0.2,0.2l-0.5,0.6l-0.3,0.1l-0.3-0.1l-0.8-0.6l-0.3-0.2l-0.7-0.1l-0.4-0.3l-0.3-0.3l-0.5-0.3h-0.6h-1.9l-1-0.2h-0.6l-0.7,0.2l0,0l-1.4-0.1l-0.3-1l-0.2-1.1l-1-0.8l-0.2-0.4l-0.3-0.3l-0.5,0.4l-0.2,0.4l-0.1,1.2l-0.2,0.4l0.4,0.3l0.5,0.7l0.4,0.3l-1.3-0.1l-0.9-0.4h-1l-1.3,1l1.4,0.5l0.6,0.3l0.5,0.6l-0.3,0.7l-1,1.3l-0.2,0.7v0.4l-0.1,0.2l-0.5,0.5l-0.8,0.5l-3.2,1l0.9,0.6l0.7,0.8l-11.6-2.9l-2.2-0.9l-0.2-0.4l-0.4-1.6l-0.2-0.4l-9.8-3l-9.6-1.7l-8.1-2.1l-5.6-0.7l-0.9-0.6l0.9-0.9l-1.4-2.1l-0.2-1v-3.8l-0.2-0.6l-2.2-2.3l-0.9-0.6l-1-0.1l-1,0.1l-4.1,1.3l-1,0.6l-0.5,1l-0.9,1.1l-0.5,0.8v0.4l0.2,0.5l0.2,1.4l0.3,0.2h0.4l0.6,0.4h0.5l0.3,0.1l0.2,0.5v0.3v0.3v0.1l1.3,2.3l0.3,1h-0.9l-0.7-0.2l-3.4-3.3l-1.2-0.7l-3-0.6l-1.3-0.9l0.6-1.1l0.2-0.2l-0.8-0.5l-1.1-0.1l-2.1,0.1l-1.6,0.3l-0.3,0.2l-0.6,0.6v0.4l0.2,0.3l-0.1,0.5l-0.3,1.3l-0.4,0.4l-1.2-0.8l-0.6-0.3l-2-0.3l-0.5-0.3l-0.6-0.9l-0.1-0.3l0.1-0.8v-0.3l-0.3-0.1l-0.6,0.1h-0.3l-2.3-0.7l-2.5,0.2l-4.8,1.4l-0.4,0.3l-0.3,0.5l-0.4,0.1l-2.3-2.2l-0.2-0.4l-0.4-1.2l-1-0.5l-10.4,1.1h-2.3l-2.4-1.1l-3.5-3.7l-2.5-0.9l-2.7,0.1l-8.3,3.1l-5,0.8l-3.3,1.7l-1.2,0.3l-0.5-0.1l-0.5-0.5l-0.4-0.3l-0.5,0.2l-0.5,0.2l-0.6,0.2l-1.3-0.1l-1.2-0.3l-1-0.4l-0.7-0.7l-2.7-4.6l-1.5-1.9l-2.3-1.1l-2,0.1l-0.5-0.3l-0.4-0.7l-0.2-0.7l-0.3-0.5l-0.7-0.2h-5l-10.6-2.1l-3.7,0.6l-3.1-0.2l-1.1-0.6l0.4-1.1l-1.7,0.1l-1.9,0.4l-0.8,0.5l-1.3,1.2l-0.9,0.2l-0.4-0.2l-0.2-0.2h-0.3l-0.7,0.7l-0.5,0.3l-0.6,0.2l-0.5-0.1l-0.2-0.4l-0.3,0.1l-2.1,1.6l-2.1,0.3l-2-0.4l-1.8-0.6l-1.9-0.3l-1.6-0.8l-1.3-1.9l-1.8-3.9l-1.8-2.4l-2.2-0.5l-2.4,0.6l-2.4,1.3l-2,1.8l-1.3,0.8h-0.9l0.3-3l0.2-0.8l0.1-0.4l0.1-0.2l-0.1-0.6l-0.6-1.6l-0.9-0.8l-1.2-0.3l-1.5-0.1l-1.3,0.1l-3.3,0.8l-0.7-0.1l-1.2-0.7l-0.7-0.1l-0.7,0.1l-1.1,0.3l-0.6,0.1l-1.5-0.2l-4-1.3l0.5-0.4l-7.9-0.6l-0.8-0.5l-0.4-1l-0.4-3.4l-1.4-3.5l-0.7-2.8l-0.5-1.3l-0.6-0.6l-0.1-0.3l-1.3-1.6l-0.3-0.1l-0.7,0.1h-0.2l-0.1-0.3l-0.2-0.8l-0.8-2.5l-0.2-1.2l-0.6-1.3l-0.1-0.8l0.3-1.5l1.9-2.1l0.6-1.4l-0.8-2.2l-3.9-4.5l0.3-1.8l-0.4-0.5l-0.3-3.1l-0.4-1.5l-0.7-1.3l-1.1-1.1l-0.3-0.6l-0.2-0.6l-0.2-1.5v-0.7l1-8.6l-0.2-3.2l-3.8-16.1l-0.8-1.2l-2-1.8l-0.7-1.1l0.1-1.1l-1.8-1.3l-0.6-0.7l0.8,0.1l0.7-0.3l0.6-0.4l0.7-0.3l-0.5-0.5l-0.1-0.6l0.2-0.7l0.4-0.6l-1.8,0.9l-0.6,0.1l-0.6-0.2l-0.3-0.3l-0.2-0.3l-0.3-0.2l-0.3-0.2l-0.3-0.4l-0.4-0.3l-1.2,0.6l-0.3-0.3l-0.2-0.5v-0.7l-0.7,0.1l-0.4-0.3v-0.5l0.6-0.3l0.3-0.2l1-1.2l0.5-0.4v-0.5l-1.7-0.3l-1.4-1l-1-1.4l-0.3-1.6l-0.7,0.7l-0.8,0.3h-1.6l-0.8-0.3l-0.6-0.7l-0.4-0.6l-0.6-0.3l-6.1-0.1l-1.3-0.4l-0.4,0.5l-1.4-0.9l-1.8-0.3l-3.6-0.2l-1.7-0.4l-3.1-1.3l-1.8-0.3l-3.6,0.2l-1.9,0.5l-1.3,1l-1.3,0.7l-3.8,0.1l-1.6,0.4l-0.4,0.3l-1,1l-0.2,0.3l-0.1,0.8l-0.3,0.2l-0.5,0.1l-0.5,0.4l-1,0.9l-3.9,2.5l-1.5,1.2v0.3l-0.3,0.2l-1,1l-0.7,0.2l-2.6,0.4l-2.4,0.6h-0.6h-2l-0.6,0.1l-0.9,0.7l-0.5,0.1h-2.2l-1.9-0.4l-0.5-0.1l-1.2,0.6l-1.9,1.9l-0.8,0.4l-0.6,0.5l-3.2,3.8l0.9-0.3l0.3-0.2l0.5-0.5l0.2,1.7l-0.4,2.1l-0.6,1.9L715,923l-1.9,1.8l-2.2,1.2l-2.4,0.5l-2.7-0.1l-4.7-1.7l-2.7-0.4l-2.2,1.1l-0.7,1.3l-0.3,1.2l-0.6,1l-1.4,0.3l-1.1,0.2l-2.6,0.8l-0.9,0.4l-3.8,3.6l-0.7,0.4l-5.6,4.9l-6.3,3.9l-0.4,0.4l-0.4,0.4l-0.4,0.4l-0.7,0.2l-0.7-0.2l-1-0.6l-0.7-0.1l-5,0.4l-2.6-0.4l-1-1.6l-0.7-2l-1.7-1.7l-2.6-0.5l-5.3,0.2l-2.2-1.1l-1-1.8l-0.9-2.2l-1.1-2.1l-1.7-1.5l-1.3-0.2l-1.1,0.2l-1.2,0.3l-4.4,0.4l-1.3-0.2l-4-1.2l-1-0.2l-0.6-0.2l-1.1-1l-0.5-0.2H625l-1.3,0.2l-3.8,1.9l-2.7,0.4l-2.4,0.7l-1.3,0.1l-2.6-0.9l-1.4-0.1l-1.4,0.7l-0.7-0.2l-3-2.8l-4.4-2.8l-5.7-4.5l-0.9-1.1l-0.3-1.3l-0.1-3.3l-0.5-1.4l-1-1.3l-1.9-1.2l-19.9-7.1l-1.3-0.2l-1.2-0.3l-0.8-1l-0.6-1.1l-0.8-0.9l-3.4-0.9l-0.6-0.7l-0.5-1.5l-1.2-0.8l-2.7-0.8l-4.7-4.5l-2.1-1.5l-7.6-3.5l-1.2-1.4l-0.1-1.4l0.5-0.9l1-0.4l1.2-0.1h1.1l1.3-0.1l0.7-0.7l-0.5-1.6l-0.9-0.9l-2.4-0.9l-0.9-0.8l-0.5-0.8l-0.9-2.3l-0.4-0.7l-4.4-4.7l-1.9-1.6l-2.2-1l-10.4-2.4l-2.2-1.2l-6.9-6.7l-2.2-1.5l-2.4-1.1l-2.8-0.4l-4,0.6l-1-0.3l-1.1-0.8l-1.4-0.4h-2.9l-3.4,0.8l-1.2,0.1l-6.4-0.5l-0.7-0.2l-0.3-0.5l-0.1-0.6l-0.2-0.5l-0.3-0.4l-1.6-0.5l-1.2-1l-2.7-2.9l-0.7-1l-0.6-1.3l-0.2-1.7l-0.6-1.1l-1.5-0.7l-2.7-0.8l-1.2-0.9l-4.1-4.1l-0.5-0.7l-0.2-1l-0.1-1.8l1.3-3.7l-0.1-1.9l-1.2-2l-2-1.9l-0.7-0.9l-2.1-3.4l-1.9-2.1l-0.5-0.7l-3.5-9.2l-0.5-2.2l-0.1-8.8l-0.7-3l-1.3-2.5l-1.5-1.8l-1.9-1.2l-2.5-0.6l-2.4-0.2l-1.1-0.3l-0.5-0.7l-0.5-1.4l-2.7-3.6l-0.5-1.3l-0.3-1.9l0.2-1.7l1.2-0.8l1.1,0.5l1.2,1l0.9,1.2l0.6,1.2l0.6-0.6l-0.1-0.5l-0.2-0.6l0.1-0.7l0.4-0.5l1.2-1.1l0.4-0.8l0.2-1.5l-0.2-1.6l-0.5-1l-1.1,0.3l-0.5-2l-0.4-0.7l-0.7-0.6l-0.4,0.1l-0.5,0.3l-0.5,0.1l-0.2-0.3l-0.1-1.2l-0.1-0.5l-0.2-0.4l-1.4-0.3l-4.6,0.3l-1.1,0.2l-1.5,1l-1.6-0.2l-1.3-1.2l-0.5-1.9l-0.2-1.7l0.2-0.8l0.5-0.9l0.4-0.9l0.4-1.2l0.6-0.5l0.8,1l0.3-2.8l0.1-0.5l-0.5-0.2l-0.4-0.4l-0.7-1.3l0.4-1.7v-2.7l-0.3-2.7l-0.5-1.9l-0.7-1.4l-1.2-1.7l-0.9-0.4v2.1l-0.3-0.8l-1.7-2.6l-3.1-2.6l-0.5-0.9l-0.4-1.2l-0.9-1.3l-1.9-2l-3.5-1.4l-0.5-0.7l-0.4-1.4l-0.8-1.3l-1.6-1.8l-1.6-2.4l-2.6-5l-1.4-2.1l-1.1-1l-2.5-1.5l-2.2-2.4l-0.2-0.3l-0.2-0.8l-0.1-1.3l-0.2-0.7l0.9-0.1l0.3-0.4l-0.4-0.5l-0.8-0.4l0.7-2.4l-1.4-3.9l0.4-1.8l-0.9-0.7l-0.9-1.2l-0.8-1.4l-0.3-1.2l-0.3-0.7l-0.9-0.6l-2-0.8l-2.1-0.3l-2.2,0.4l-2.1,0.7l-18.4,12.1l-2.1,0.9l-1.9-0.5l-1.6-2.4l-0.2-1.1v-3.2l-0.5-1.2l-0.4-0.6l-0.1-0.4l-0.3-0.2l-0.6-0.4l-0.6-0.3l-0.5-0.1l-1.3-0.1l-0.6,0.1l-1.3,0.3l-0.7,0.1l-0.6-0.2l-0.9-0.6l-0.5-0.2l-1.2,0.2l-2.2,1l-1.2,0.2l-1.5-0.1l-0.6-0.6l0.1-2.8l-0.1-0.2l-0.9-0.6l-0.2-0.4v-0.4v-1l0.1-0.6l0.2-0.4v-0.4l-0.7-0.5l-0.3,1.2l-0.7,1.1l-0.8,0.8l-1,0.2l-1.1-0.7l-0.5-0.9l-0.6-0.7l-1-0.1l-1.4-0.5l-3.8-2.3l-0.8-0.7l-0.4-2.3l-1.1-1.4l-1.5-0.8l-1.9-0.5l0.7-1.1l0.9-0.3l2.4,0.4h1.3l1.9-0.7l1.1-0.2l1.2,0.3l2.4,1.3l0.8,0.3l1.3,0.2l1,0.4l0.8,0.7l0.7,1.1l0.4-0.9l1.1-2.1l1.7-2.2l0.3-0.7l0.1-1.2l-1.2,0.2l-0.9-0.6l-0.5-1l-0.5-2.5l-0.7,0.3l-0.9,1l-0.9,0.7l0.1-0.9l0.1-0.2l0.2-0.3l-0.5-0.8l-0.5,0.1l-0.6,0.5l-0.8,0.2l-0.4-0.3l-0.6-0.9l-0.4-0.2h-0.4l-0.5,0.4h-0.3l-1.2-0.2l-1-0.3h-1l-1,0.5l-2.1-0.3l-1.7,1.1l-0.4,1.4l1.6,0.7l1.8,0.4l1.5,0.9l0.4,1.3l-1.1,1.2h-1l-3.2-0.5l-0.7,0.2l-3.2,3.1l-0.2,0.3l-0.5,0.8l-0.3,0.9l0.7,0.6l-0.3,0.5l-0.4,0.5l-0.2,0.4l0.5,1.5l1,1l1.2,1l0.9,1l0.5,1.3l0.4,1.5l0.3,3.1l-0.1,0.9l-0.5,1.4l-0.2,0.8l0.1,0.7l0.3,1.3v0.8l-0.3,1.4l-0.8,1.2l-1.1,0.9l-1.2,0.3l-3.9-0.4l-1.1,0.4l-1.1-0.5h-4.1l-2.5-1.4l-0.9-0.2l-0.2,1.2l0.3,0.8l0.8,1.3l0.1,1l-0.1,0.7l-0.5,0.6l-0.5,0.4l-0.5,0.4l-1.3,0.4l-4.3-0.4v-0.5l-0.3,0.4l-0.1,0.2v0.4l1.4-0.1l0.3,0.7l-0.8,0.8l-1.5,0.4l-6.4-0.6l-4.4-1.6l-2.1-1.6l-2.1-0.7l-3.2-2.1l-2.6-0.9l-2.7-0.5h-2.5l-2.2,0.6l-4.1,2.3l-0.4-1.9l-0.2-2.1l-0.4-1.9l-1-1.3l0.7,2.3l0.1,0.8l-0.1,0.9l-0.3,0.9v0.7l0.4,0.6v1.6l0.4,1.2l0.6,1.1l0.6,1.3l0.2,1.5v2.5l0.2,1.7l0.8,2.2l1.5,3.3l1.8,2.6l1.5-0.1l1,3.1l1.4,3.1l2.5,3.6l0.4,1.6l-0.5,1.5l-1.3,0.5l-1.4-0.3l-1.3-0.8l-0.4-0.6l-0.1-0.7l-0.3-0.6l-0.8-0.4l-0.9-0.1h-0.8l-0.8-0.1l-0.7-0.8h1.2l-0.7-1l-1.4-0.4l-1.3-0.1l-0.6,0.3L269.3,730.4"
}];

var iransIslandsProperties = [{
  id: "b34",
  parentId: "a1",
  name: "khark",
  persianName: "خارک",
  persianNickName: "خارک",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "407.2,756.3 406.5,754 406.3,751.2 408.7,751.7 408.8,751.8 409.9,750.7 410.8,753.5 410.6,755.1 410.4,756.6 409.3,759.7 	"
}, {
  id: "b35",
  parentId: "a1",
  name: "kish",
  persianName: "کیش",
  persianNickName: "کیش",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "621.2,946 618.8,944.8 617.2,942 618.2,940.3 619.4,939.4 620.7,939 622.2,939.1 623.3,939.4 625.4,939.7 626.9,940.3 627.1,941.4 627.1,942 627.2,942 627.3,942.2 628,942.9 628.2,944.2 627.7,945.6 626.5,946.3 	"
}, {
  id: "b36",
  parentId: "a1",
  name: "hormoz",
  persianName: "هرمز",
  persianNickName: "هرمز",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "765.5,906.9 765.8,904 767.2,902.1 769.1,901.5 769.9,902.2 770.7,902.4 771.5,903.3 772,904.8 771.7,906.2 770.8,907.1 769.7,907.8 768.3,907.9 	"
}, {
  id: "b37",
  parentId: "a1",
  name: "gheshm",
  persianName: "قشم",
  persianNickName: "قشم",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "698.8,941.7 698.4,940.6 698,938.5 698.5,937.2 698.5,937 698.4,936.8 697.5,933.9 699,932.2 701.9,933.4 702.5,933 703.1,933.2 705.9,931.6 713.9,928.8 715,928.7 715.8,928.3 718.4,926.7 719.6,925.7 723.7,923.9 724.6,923.9 725.7,924 726,924 726.2,923.9 726.7,923.5 726.4,922.8 727.5,921.6 727.6,920.7 727.4,917.9 727,917 726.1,916.1 725.2,915.3 724.2,913.7 726.8,912 735.2,915.4 736.9,914.9 743.1,910.7 751.1,908.8 753.6,908.8 755,909.1 756.8,909.9 758.4,911.2 759.1,913.4 756.6,915.1 752.9,916.1 752,917 750.7,920 750,921.3 747.6,923.9 747.2,924.7 746.5,925.6 744.3,926.8 743.8,927.4 743.3,927.7 740.4,930.7 738.1,932 736.2,931.2 734.7,929.7 733.8,928.9 730.6,930.6 729.6,931.6 728.1,932.5 726.6,932.5 724,932.1 723.1,932.3 722.1,932.9 718.9,935.2 715.6,936.7 713.6,938.3 712.3,938.9 708.6,939.4 706.3,940 705.3,940.7 704.4,941.2 703.4,941 703.1,940.8 702.7,941.5 701.8,942.1 700.9,942.4 699.7,942.6 	"
}, {
  id: "b38",
  parentId: "a1",
  name: "lark",
  persianName: "لارک",
  persianNickName: "لارک",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "759,922 759.3,919.1 760.5,917.5 762.4,916.6 765.7,916.2 766.2,919.9 763.9,922 761.1,923 	"
}, {
  id: "b39",
  parentId: "a1",
  name: "lavan",
  persianName: "لاوان",
  persianNickName: "لاوان",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "581.9,925.4 578.2,924.8 577,924.2 576,923.5 574.2,921.9 572.8,920.5 574,919.3 574.6,919.2 575.2,919 576,918.8 581.1,920.4 585.6,920.8 587.2,921.6 590,924.2 587.1,924.8 584.9,924.6 584.5,924.7 583.3,925.4 	"
}, {
  id: "b40",
  parentId: "a1",
  name: "faror",
  persianName: "فارور",
  persianNickName: "فارور",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "653.4,962.4 652.6,961.9 651.8,961.1 651.8,960 651.6,959.3 651.6,958.3 651.9,957.2 652.6,956.4 653.6,955.7 654.9,956.2 655.5,956.8 655.8,957 656.4,957.4 656.8,958 657.2,959.1 655.6,962.4 654.6,962.8 	"
}, {
  id: "b41",
  parentId: "a1",
  name: "hendorabi",
  persianName: "هندورابی",
  persianNickName: "هندورابی",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "602,934.5 600.7,933.7 599.5,932.2 600.7,930.3 602.5,930.3 603.3,930.6 604.4,931 605.4,933 603.7,934.7 	"
}, {
  id: "b42",
  parentId: "a1",
  name: "hengam",
  persianName: "هنگام",
  persianNickName: "هنگام",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "731.5,936.7 731.7,934.2 732.6,932.4 733.9,931.3 735.4,931 736.4,932.5 736.6,934.8 735.4,936.6 733.6,937.9 	"
}, {
  id: "b43",
  parentId: "a1",
  name: "siri",
  persianName: "سیری",
  persianNickName: "سیری",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "654.7,987.2 653.3,986.5 652.8,984.6 654.2,983.6 656.6,982.9 657.3,984.4 657.5,986.4 656.1,987.5 	"
}, {
  id: "b44",
  parentId: "a1",
  name: "abumusa",
  persianName: "ابوموسی",
  persianNickName: "ابوموسی",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "687.5,986.8 688.8,986 690.7,986.5 690.8,988.2 690.2,990.6 688.5,990.5 686.8,989.6 686.5,987.9 	"
}, {
  id: "b45",
  parentId: "a1",
  name: "tonbebozorg",
  persianName: "تنب بزرگ",
  persianNickName: "تنب بزرگ",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "704,961.8 703.6,962.7 702.3,962.9 701.7,962 701.3,960.4 702.3,960 703.6,959.9 704.3,960.9 	"
}, {
  id: "b46",
  parentId: "a1",
  name: "tonbekuchak",
  persianName: "تنب کوچک",
  persianNickName: "تنب کوچک",
  ltrRotate: "",
  ltrX: "",
  ltrY: "",
  points: "693.7,963.1 693.5,963.4 693,963.5 692.8,963.2 692.6,962.6 693,962.4 693.5,962.3 693.8,962.7 	"
}];

var IranMap = function IranMap(props) {
  return /*#__PURE__*/React.createElement("div", {
    style: {
      height: props.height,
      width: props.height * (1070.6 / 980),
      backgroundColor: props.backgroundColor
    }
  }, /*#__PURE__*/React.createElement("svg", {
    version: "1.1",
    id: "iran",
    xmlns: "http://www.w3.org/2000/svg",
    x: "0px",
    y: "0px",
    viewBox: "0 0 1200 1070.6",
    enableBackground: "new 0 0 1200 1070.6",
    style: {
      width: '100%',
      height: '100%'
    }
  }, /*#__PURE__*/React.createElement("g", {
    id: "provinces"
  }, iransStatesProperties.map(function (iranState, index) {
    return /*#__PURE__*/React.createElement("path", {
      key: index,
      id: iranState.persianName,
      onClick: function onClick() {
        return props.onClick(iranState);
      },
      "data-tip": "" + props.data[iranState.name],
      "data-for": iranState.name + "Tooltip",
      fill: props.selectedArea === iranState.name ? props.selectedAreaColor : "rgba(" + props.defaultAreasColor + "," + props.data[iranState.name] / props.maxValue,
      stroke: "#9B9B9B",
      style: {
        cursor: 'pointer'
      },
      d: iranState.d
    });
  }), iransSeasProperties.map(function (iranSea, index) {
    return /*#__PURE__*/React.createElement("path", {
      key: index,
      id: iranSea.persianName,
      onClick: function onClick() {
        return props.onClick(iranSea);
      },
      "data-tip": "" + props.data[iranSea.name],
      "data-for": iranSea.name + "Tooltip",
      fill: props.selectedArea === iranSea.name ? props.selectedAreaColor : '#00BDFF',
      stroke: "#9B9B9B",
      style: {
        cursor: 'pointer'
      },
      d: iranSea.d
    });
  })), /*#__PURE__*/React.createElement("g", {
    id: "islands"
  }, iransIslandsProperties.map(function (iranIsland, index) {
    return /*#__PURE__*/React.createElement("polygon", {
      key: index,
      id: iranIsland.persianName,
      onClick: function onClick() {
        return props.onClick(iranIsland);
      },
      "data-tip": "" + props.data[iranIsland.name],
      "data-for": iranIsland.name + "Tooltip",
      fill: props.selectedArea === iranIsland.name ? props.selectedAreaColor : "rgba(" + props.defaultAreasColor + "," + props.data[iranIsland.name] / props.maxValue,
      stroke: "#9B9B9B",
      points: iranIsland.points
    });
  })), iransStatesProperties.map(function (iranState, index) {
    return /*#__PURE__*/React.createElement("text", {
      key: index,
      textAnchor: "start",
      x: "" + iranState.ltrX,
      y: "" + iranState.ltrY,
      onClick: function onClick() {
        return props.onClick(iranState);
      },
      fill: props.selectedArea === iranState.name ? props.selectedAreaTextColor : '#000',
      style: {
        fontSize: 16,
        fontWeight: 'bold',
        cursor: 'pointer',
        transform: "rotate(" + iranState.ltrRotate + "deg)",
        letterSpacing: 'normal'
      },
      "data-tip": "" + props.data[iranState.name],
      "data-for": iranState.name + "Tooltip"
    }, iranState.persianNickName);
  }), iransSeasProperties.map(function (iranSea, index) {
    return /*#__PURE__*/React.createElement("text", {
      key: index,
      textAnchor: "start",
      x: "" + iranSea.ltrX,
      y: "" + iranSea.ltrY,
      fill: props.selectedArea === iranSea.name ? props.selectedAreaTextColor : '#000',
      onClick: function onClick() {
        return props.onClick(iranSea);
      },
      style: {
        fontSize: 16,
        fontWeight: 'bold',
        cursor: 'pointer',
        transform: "rotate(" + iranSea.ltrRotate + "deg)",
        letterSpacing: 'normal'
      },
      "data-tip": "" + props.data[iranSea.name],
      "data-for": iranSea.name + "Tooltip"
    }, iranSea.persianNickName);
  })), iransStatesProperties.map(function (state, index) {
    return /*#__PURE__*/React.createElement(ReactTooltip, {
      key: index,
      id: state.name + "Tooltip",
      textColor: "#000000FF",
      backgroundColor: "#FFFFFFFF"
    });
  }), iransIslandsProperties.map(function (island, index) {
    return /*#__PURE__*/React.createElement(ReactTooltip, {
      key: index,
      id: island.name + "Tooltip",
      textColor: "#000000FF",
      backgroundColor: "#FFFFFFFF"
    });
  }), iransSeasProperties.map(function (island, index) {
    return /*#__PURE__*/React.createElement(ReactTooltip, {
      key: index,
      id: island.name + "Tooltip",
      textColor: "#000000FF",
      backgroundColor: "#FFFFFFFF"
    });
  }));
};

IranMap.propTypes = {
  height: propTypes.number.isRequired,
  backgroundColor: propTypes.string,
  onClick: propTypes.func.isRequired,
  selectedArea: propTypes.string.isRequired,
  defaultAreasColor: propTypes.string,
  selectedAreaColor: propTypes.string,
  selectedAreaTextColor: propTypes.string,
  unselectedAreaTextColor: propTypes.string
};

var testData = {
  alborz: 10,
  ardebil: 20,
  azerbaijansharghi: 30,
  azerbaijangharbi: 40,
  bushehr: 34,
  chvab: 67,
  fars: 12,
  gilan: 1,
  golestan: 54,
  hamedan: 67,
  hormozgan: 32,
  ilam: 66,
  esfehan: 42,
  kerman: 13,
  kermanshah: 12,
  khorasanshomali: 1,
  khorasanrazavi: 30,
  khorasanjunubi: 78,
  khuzestan: 55,
  kvab: 7,
  kordestan: 43,
  lorestan: 45,
  markazi: 2,
  mazandaran: 33,
  ghazvin: 18,
  ghom: 29,
  semnan: 23,
  svab: 61,
  tehran: 56,
  yazd: 17,
  zanjan: 77,
  khazar: 54,
  khalijefars: 41,
  khark: 61,
  kish: 34,
  hormoz: 48,
  gheshm: 58,
  lark: 4,
  lavan: 55,
  faror: 23,
  hendorabi: 21,
  hengam: 4,
  siri: 2,
  abumusa: 34,
  tonbebozorg: 12,
  tonbekuchak: 53
};

var InteractiveIranMap = function InteractiveIranMap(_ref) {
  var _ref$data = _ref.data,
      data = _ref$data === void 0 ? testData : _ref$data,
      _ref$height = _ref.height,
      height = _ref$height === void 0 ? 600 : _ref$height,
      _ref$defaultAreasColo = _ref.defaultAreasColor,
      defaultAreasColor = _ref$defaultAreasColo === void 0 ? '255,0,0' : _ref$defaultAreasColo,
      _ref$selectedAreaColo = _ref.selectedAreaColor,
      selectedAreaColor = _ref$selectedAreaColo === void 0 ? '#00f' : _ref$selectedAreaColo,
      _ref$selectedAreaText = _ref.selectedAreaTextColor,
      selectedAreaTextColor = _ref$selectedAreaText === void 0 ? '#fff' : _ref$selectedAreaText,
      _ref$unselectedAreaTe = _ref.unselectedAreaTextColor,
      unselectedAreaTextColor = _ref$unselectedAreaTe === void 0 ? '#000' : _ref$unselectedAreaTe,
      _ref$backgroundColor = _ref.backgroundColor,
      backgroundColor = _ref$backgroundColor === void 0 ? '#fff' : _ref$backgroundColor,
      _ref$defaultSelectedA = _ref.defaultSelectedArea,
      defaultSelectedArea = _ref$defaultSelectedA === void 0 ? 'tehran' : _ref$defaultSelectedA;

  var _React$useState = React.useState({
    selectedArea: defaultSelectedArea
  }),
      state = _React$useState[0],
      setState = _React$useState[1];

  var selectAreaHandler = function selectAreaHandler(area) {
    setState(function (prevState) {
      return _extends({}, prevState, {
        selectedArea: area.name
      });
    });
  };

  var arr = Object.values(data);
  var max = Math.max.apply(Math, arr);
  return /*#__PURE__*/React.createElement("div", null, /*#__PURE__*/React.createElement(IranMap, {
    onClick: selectAreaHandler,
    height: height,
    data: data,
    maxValue: max,
    selectedArea: state.selectedArea,
    defaultAreasColor: defaultAreasColor,
    selectedAreaColor: selectedAreaColor,
    selectedAreaTextColor: selectedAreaTextColor,
    unselectedAreaTextColor: unselectedAreaTextColor,
    backgroundColor: backgroundColor
  }));
};

module.exports = InteractiveIranMap;
//# sourceMappingURL=index.js.map
