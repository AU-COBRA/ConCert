var FirstandthirdToc = (function () {
'use strict';

function findOne(selector, el) {
  var found = find(selector, el);

  if (found.length) {
    return found[0];
  }

  return null;
}

function isWindow(obj) {
  return obj != null && obj === obj.window;
}

function find(selector) {
  var context = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;

  if (selector instanceof HTMLElement || selector instanceof Node || isWindow(selector)) {
    return [selector];
  } else if (selector instanceof NodeList) {
    return [].slice.call(selector);
  } else if (typeof selector === 'string') {
    var startElement = context ? findOne(context) : document;
    return [].slice.call(startElement.querySelectorAll(selector));
  }
  return [];
}

function addClass(selector, cls) {
  if (Array.isArray(selector)) {
    return selector.forEach(function (item) {
      return addClass(item, cls);
    });
  }
  var els = find(selector);
  if (els.length) {
    var clsArray = [].concat(cls);
    els.forEach(function (el) {
      clsArray.forEach(function (item) {
        el.classList.add(item);
      });
    });
    return els;
  }
}

function on(selector, event, cb) {
  var capture = arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : false;

  if (Array.isArray(selector)) {
    selector.forEach(function (item) {
      return on(item, event, cb, capture);
    });
    return;
  }

  var data = {
    cb: cb,
    capture: capture
  };

  if (!window._domassistevents) {
    window._domassistevents = {};
  }

  window._domassistevents['_' + event] = data;
  var el = find(selector);
  if (el.length) {
    el.forEach(function (item) {
      item.addEventListener(event, cb, capture);
    });
  }
}

var NativeCustomEvent = window.CustomEvent;

//
// Check for the usage of native support for CustomEvents which is lacking
// completely on IE.
//
function canIuseNativeCustom() {
  try {
    var p = new NativeCustomEvent('t', {
      detail: {
        a: 'b'
      }
    });
    return p.type === 't' && p.detail.a === 'b';
  } catch (e) {
    return false;
  }
}

// Lousy polyfill for the Custom Event constructor for IE.
var IECustomEvent = function CustomEvent(type, params) {
  var e = document.createEvent('CustomEvent');

  if (params) {
    e.initCustomEvent(type, params.bubbles, params.cancelable, params.detail);
  } else {
    e.initCustomEvent(type, false, false, undefined);
  }

  return e;
};

var DomassistCustomEvent = canIuseNativeCustom() ? NativeCustomEvent : IECustomEvent;

function fire(selector, type, params) {
  if (Array.isArray(selector)) {
    return selector.forEach(function (item) {
      return fire(item, type, params);
    });
  }
  var els = find(selector);

  if (els.length) {
    els.forEach(function (el) {
      var event = new DomassistCustomEvent(type, params);
      el.dispatchEvent(event);
    });

    return els;
  }
}

function removeClass(selector, cls) {
  if (Array.isArray(selector)) {
    return selector.forEach(function (item) {
      return removeClass(item, cls);
    });
  }

  var els = find(selector);
  if (els.length) {
    var clsArray = [].concat(cls);
    els.forEach(function (el) {
      clsArray.forEach(function (item) {
        el.classList.remove(item);
      });
    });
    return els;
  }
}

var SCROLLABLE_CONTAINER = void 0;

function getScrollableContainer() {
  if (SCROLLABLE_CONTAINER) {
    return SCROLLABLE_CONTAINER;
  }

  var documentElement = window.document.documentElement;
  var scrollableContainer = void 0;

  documentElement.scrollTop = 1;

  if (documentElement.scrollTop === 1) {
    documentElement.scrollTop = 0;
    scrollableContainer = documentElement;
  } else {
    scrollableContainer = document.body;
  }

  SCROLLABLE_CONTAINER = scrollableContainer;

  return scrollableContainer;
}

SCROLLABLE_CONTAINER = getScrollableContainer();

var setupReady = function setupReady(callbacks) {
  return function (callback) {
    callbacks.push(callback);
    function execute() {
      while (callbacks.length) {
        var fn = callbacks.shift();
        if (typeof fn === 'function') {
          fn();
        }
      }
    }
    function loaded() {
      document.removeEventListener('DOMContentLoaded', loaded);
      execute();
    }

    setTimeout(function () {
      if (document.readyState !== 'loading') {
        return execute();
      }
    }, 0);

    document.addEventListener('DOMContentLoaded', loaded);
  };
};
var ready = setupReady([]);

function styles(selector, css) {
  if (Array.isArray(selector)) {
    selector.forEach(function (item) {
      return styles(item, css);
    });
  }
  var els = find(selector);
  if (els.length) {
    els.forEach(function (el) {
      Object.keys(css).forEach(function (key) {
        el.style[key] = css[key];
      });
    });
  }
}

/* global DocumentTouch */

/* global window */

var attrobj = function (key, el) {
  var values = {};

  Object.keys(el.dataset).forEach(function (data) {
    if (data.match(new RegExp('^' + key)) && data !== key) {
      var optionName = data.replace(key, '');
      var isGlobal = false;

      if (optionName.match(/^Global/)) {
        optionName = optionName.replace('Global', '');
        isGlobal = true;
      }

      optionName = '' + optionName[0].toLowerCase() + optionName.slice(1);

      if (isGlobal) {
        values[optionName] = window[el.dataset[data]];
      } else {
        values[optionName] = el.dataset[data];
      }
    }
  });

  return values;
};

var debounce = function debounce(func, wait, immediate) {
  var timeout = void 0;
  return function () {
    var context = this;
    var args = arguments; // eslint-disable-line prefer-rest-params
    var later = function later() {
      timeout = null;
      if (!immediate) {
        func.apply(context, args);
      }
    };
    var callNow = immediate && !timeout;
    clearTimeout(timeout);
    timeout = setTimeout(later, wait);
    if (callNow) {
      func.apply(context, args);
    }
  };
};

var asyncGenerator = function () {
  function AwaitValue(value) {
    this.value = value;
  }

  function AsyncGenerator(gen) {
    var front, back;

    function send(key, arg) {
      return new Promise(function (resolve, reject) {
        var request = {
          key: key,
          arg: arg,
          resolve: resolve,
          reject: reject,
          next: null
        };

        if (back) {
          back = back.next = request;
        } else {
          front = back = request;
          resume(key, arg);
        }
      });
    }

    function resume(key, arg) {
      try {
        var result = gen[key](arg);
        var value = result.value;

        if (value instanceof AwaitValue) {
          Promise.resolve(value.value).then(function (arg) {
            resume("next", arg);
          }, function (arg) {
            resume("throw", arg);
          });
        } else {
          settle(result.done ? "return" : "normal", result.value);
        }
      } catch (err) {
        settle("throw", err);
      }
    }

    function settle(type, value) {
      switch (type) {
        case "return":
          front.resolve({
            value: value,
            done: true
          });
          break;

        case "throw":
          front.reject(value);
          break;

        default:
          front.resolve({
            value: value,
            done: false
          });
          break;
      }

      front = front.next;

      if (front) {
        resume(front.key, front.arg);
      } else {
        back = null;
      }
    }

    this._invoke = send;

    if (typeof gen.return !== "function") {
      this.return = undefined;
    }
  }

  if (typeof Symbol === "function" && Symbol.asyncIterator) {
    AsyncGenerator.prototype[Symbol.asyncIterator] = function () {
      return this;
    };
  }

  AsyncGenerator.prototype.next = function (arg) {
    return this._invoke("next", arg);
  };

  AsyncGenerator.prototype.throw = function (arg) {
    return this._invoke("throw", arg);
  };

  AsyncGenerator.prototype.return = function (arg) {
    return this._invoke("return", arg);
  };

  return {
    wrap: function (fn) {
      return function () {
        return new AsyncGenerator(fn.apply(this, arguments));
      };
    },
    await: function (value) {
      return new AwaitValue(value);
    }
  };
}();





var classCallCheck = function (instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
};

var createClass = function () {
  function defineProperties(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i];
      descriptor.enumerable = descriptor.enumerable || false;
      descriptor.configurable = true;
      if ("value" in descriptor) descriptor.writable = true;
      Object.defineProperty(target, descriptor.key, descriptor);
    }
  }

  return function (Constructor, protoProps, staticProps) {
    if (protoProps) defineProperties(Constructor.prototype, protoProps);
    if (staticProps) defineProperties(Constructor, staticProps);
    return Constructor;
  };
}();

'use strict';

var Events = {
  In: 'scrolltriggers:inView',
  Out: 'scrolltriggers:outOfView',
  Pause: 'scrolltriggers:pause',
  Resume: 'scrolltriggers:resume'
};

var ScrollTrigger = function () {
  function ScrollTrigger(el, options) {
    var _this = this;

    classCallCheck(this, ScrollTrigger);

    if (el.hasAttribute('data-scroll-init')) {
      return;
    }

    this.added = false;
    this.el = el;
    this.options = options;
    this.eventHandler = debounce(this.onScroll.bind(this), 10, true);
    this.dCalcBounds = debounce(this.calcBounds.bind(this), 10);
    this.paused = false;
    this.disabled = false;

    //if image, only process once and load a screen size above
    if (this.options.image || this.options.srcset) {
      this.options.offset = Math.max((document.documentElement.clientHeight, window.innerHeight || 0) / 2) * -1;
      this.options.once = true;
    }

    el.setAttribute('data-scroll-init', 'true');

    this.calcBounds();

    window.addEventListener('scroll', this.eventHandler);
    window.addEventListener('resize', this.dCalcBounds);

    on(this.el, Events.Pause, function () {
      _this.paused = true;
    });

    on(this.el, Events.Resume, function () {
      _this.paused = false;
    });

    /*
      Prevents a bug on Blink+Webkit in which scroll is always 0 until around
      400 milliseconds due to anchor scrolling features.
     */
    setTimeout(this.eventHandler, 400);
  }

  createClass(ScrollTrigger, [{
    key: 'calcBounds',
    value: function calcBounds() {
      // Element is hidden and not fixed
      var isAllowedToBeFixed = this.options.progress === true || typeof this.options.fixed !== 'undefined';
      if (!this.el.offsetParent && !isAllowedToBeFixed) {
        // Don't even bother calculating
        this.disabled = true;
        return;
      }

      this.disabled = false;

      var position = this.options.position || 'bottom';

      this.startEl = this.options.start ? findOne(this.options.start) : this.el;
      ScrollTrigger.checkElement(this.startEl, 'start', this.options.start);
      var rect = this.startEl.getBoundingClientRect();
      var scrollY = ScrollTrigger.getScrollY();
      var start = rect.top + scrollY + (this.options.offset || 0);

      this.start = ScrollTrigger.processPosition(position, start);

      if (this.options.end) {
        var endEl = findOne(this.options.end);
        var endRect = endEl.getBoundingClientRect();
        var end = endRect.top + scrollY;
        var endPosition = this.options.positionEnd || 'bottom';
        if (endPosition === 'auto') {
          endPosition = 'top';
        }

        this.end = ScrollTrigger.processPosition(endPosition, end);

        if (this.options.positionEnd === 'auto') {
          this.end -= this.el.offsetHeight;
        }

        ScrollTrigger.checkElement(endEl, 'end', this.options.end);
      }

      this.eventHandler();
    }
  }, {
    key: 'inView',
    value: function inView() {
      var _options = this.options,
          className = _options.className,
          inView = _options.inView;


      if (className && this.el.classList) {
        addClass(this.el, className);
      }

      var image = this.options.image;
      var srcset = this.options.srcset;

      if (image) {
        if (this.el.tagName === 'IMG') {
          this.el.setAttribute('src', image);
        } else {
          styles(this.el, {
            backgroundImage: 'url(' + image + ')',
            backgroundRepeat: 'no-repeat'
          });
        }
      }

      if (srcset) {
        this.el.setAttribute('srcset', srcset);
      }

      if (typeof inView === 'function') {
        inView(this.el, this.options);
      }

      fire(this.el, Events.In, { bubbles: true, detail: this.options });

      if (this.options.once) {
        this.disabled = true;
        window.removeEventListener('scroll', this.eventHandler);
        window.removeEventListener('resize', this.dCalcBounds);
      }

      this.added = true;
    }
  }, {
    key: 'outOfView',
    value: function outOfView() {
      var _options2 = this.options,
          className = _options2.className,
          outOfView = _options2.outOfView;

      if (className && this.el.classList) {
        removeClass(this.el, className);
      }

      if (typeof outOfView === 'function') {
        outOfView(this.el, this.options);
      }

      fire(this.el, Events.Out, { bubbles: true, detail: this.options });

      this.added = false;
    }
  }, {
    key: 'onScroll',
    value: function onScroll() {
      var scroll = ScrollTrigger.getScrollY();

      if (this.paused || this.disabled) {
        return;
      }

      if (this.options.progress) {
        var perc = scroll / (document.documentElement.scrollHeight - window.innerHeight);
        this.el.style.width = perc * 100 + '%';
      }

      if (scroll < this.start || this.end && scroll > this.end) {
        if (this.added) {
          this.outOfView();
        }
        return;
      }

      if (this.added) {
        return;
      }
      this.inView();
    }
  }], [{
    key: 'checkElement',
    value: function checkElement(element, position, selector) {
      if (!element) {
        throw new Error(position + ' element doesn\'t match any element with selector: "' + selector + '"');
      }
    }
  }, {
    key: 'getScrollY',
    value: function getScrollY() {
      return window.pageYOffset || document.documentElement.scrollTop;
    }
  }, {
    key: 'processPosition',
    value: function processPosition(position, currentValue) {
      if (position === 'top') {
        return currentValue;
      }
      if (position === 'middle') {
        currentValue -= window.innerHeight / 2;
      } else if (position === 'bottom') {
        currentValue -= window.innerHeight;
      } else {
        currentValue -= window.innerHeight * (parseInt(position, 10) / 100);
      }
      return currentValue;
    }
  }]);
  return ScrollTrigger;
}();

var init$2 = function init(items) {
  var instances = [];

  if (items && Array.isArray(items)) {
    items.forEach(function (item) {
      var els = find(item.el);

      if (els === null) {
        throw new Error('unknown element');
      }

      els.forEach(function (el) {
        delete item.el;
        instances.push(new ScrollTrigger(el, item));
      });
    });
  } else if (items) {
    throw new Error('please convert object to array');
  } else {
    var els = find('[data-scroll]');

    els.forEach(function (el) {
      var options = attrobj('scroll', el);

      if (options.progress !== null && typeof options.progress !== 'undefined') {
        options.progress = true;
      }
      options.className = options.class;

      if (options.offset) {
        options.offset = parseInt(options.offset, 10);
      }
      if (typeof options.once !== 'undefined') {
        options.once = true;
      }
      instances.push(new ScrollTrigger(el, options));
    });
  }

  return instances;
};

if (document.readyState !== 'complete') {
  // Avoid image loading impacting on calculations
  document.addEventListener('readystatechange', function () {
    if (document.readyState === 'complete') {
      fire(window, 'resize');
    }
  });
}

ready(init$2);

init$2.Events = Events;
init$2.ScrollTrigger = ScrollTrigger;

/* global window,document */
'use strict';

var duration = 1000;

var ease = function ease(t, b, c, d) {
  if ((t /= d / 2) < 1) return c / 2 * t * t * t * t + b; //eslint-disable-line
  return -c / 2 * ((t -= 2) * t * t * t - 2) + b;
};

var animate = function animate(startTime, start, end) {
  var callback = arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : function () {};

  var time = new Date().getTime();
  var difference = end - start;
  var goingUp = difference < 0;

  if (difference === 0) {
    return;
  }

  var to = Math.round(ease(time - startTime, start, difference, duration));

  if (!goingUp && to > end) {
    to = end;
  }

  if (goingUp && to < end) {
    to = end;
  }

  window.scrollTo(0, to);

  if (to === end) {
    setTimeout(callback);
    return;
  }

  if (to < 0) {
    return;
  }

  window.requestAnimationFrame(function () {
    return animate(startTime, start, end, callback);
  });
};

var scroll = function scroll(target, hash) {
  var offset = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : 0;
  var silent = arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : false;

  fire(target, 'smoothscroll:start', { bubbles: true });
  var rect = target.getBoundingClientRect();
  var scrollY = window.pageYOffset || document.documentElement.scrollTop;
  var adjustedOffset = Math.round(rect.top + scrollY) + offset;
  var startTime = new Date();
  if (!target.hasAttribute('tabindex')) {
    target.tabIndex = '-1';
  }

  if (!silent) {
    window.history.pushState(null, 'Scroll', hash);
  }

  animate(startTime.getTime(), scrollY, adjustedOffset, function () {
    fire(target, 'smoothscroll:end', { bubbles: true });
  });
  target.focus();
};

var listenEvent = function listenEvent(el, offset) {
  if (el.dataset.smoothActive) {
    return;
  }

  el.dataset.smoothActive = true;

  el.addEventListener('click', function (e) {
    var hash = el.getAttribute('href');
    if (hash[0] !== '#') {
      return;
    }
    e.preventDefault();

    scroll(document.querySelector(hash), hash, offset);
  });
};

var init$3 = function init() {
  var query = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : '[data-smooth]';
  var offset = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 0;

  if (!window.requestAnimationFrame) {
    return;
  }

  var els = query;

  if (typeof query === 'string') {
    els = document.querySelectorAll(query);
  }

  if (els instanceof Element) {
    els = [els];
  }

  for (var i = 0, c = els.length; i < c; i++) {
    var el = els[i];
    listenEvent(el, offset);
  }
};

window.addEventListener('DOMContentLoaded', function () {
  init$3();
});

function init(el) {
  if (!el) {
    el = find('[data-toc]');
    el.forEach(function (e) {
      return init(e);
    });
    return;
  }

  if (!el) {
    return;
  }

  var container = el.dataset.tocContainer ? findOne(el.dataset.tocContainer) | document.body : document.body;
  // const selectors = el.dataset.toc.split(',').map(s => s.trim());
  var selectors = [el.dataset.toc];
  var tocItems = [];
  var offset = el.dataset.tocOffset ? parseInt(el.dataset.tocOffset, 10) : 1;
  var i = 1;

  // Building dict
  selectors.forEach(function (selector) {
    var items = find(selector, container);

    items.forEach(function (item) {
      // Keep the id if already there
      var index = item.id || 'toc-' + i++;
      var text = item.dataset.tocTitle ? item.dataset.tocTitle.trim() : item.textContent.trim();
      var name = item.tagName.toLowerCase();
      var className = 'toc-' + name;

      // Set it if none
      if (item.id !== index) {
        item.id = index;
      }

      tocItems.push({ index: index, text: text, className: className });
    });
  });

  var html = '<ul>';
  var triggerOptions = [];

  // Building markup
  tocItems.forEach(function (item, j) {
    var nextEl = tocItems[j + 1];
    var options = {
      el: '.toc-li-' + j,
      fixed: 'true',
      start: '#' + item.index,
      position: 'top',
      positionEnd: 'top',
      className: 'toc-visible'
    };
    html += '\n<li class="toc-li-' + j + ' ' + item.className + '"><a href="#' + item.index + '">' + item.text + '</a></li>';

    if (nextEl) {
      options.end = '#' + nextEl.index;
    }

    triggerOptions.push(options);
  });

  html += '</ul>';

  el.innerHTML += html;
  var tocs = find('li', el);
  var anchors = find('a', el);

  // Setting up scroll triggers and smooth scroll
  init$2(triggerOptions);
  init$3(anchors, offset);

  // Pause scroll triggers while smoothscrolling
  on(document.body, 'smoothscroll:start', function () {
    fire(tocs, 'scrolltriggers:pause');
  });

  on(document.body, 'smoothscroll:end', function () {
    fire(tocs, 'scrolltriggers:resume');
    fire(window, 'scroll');
  });

  if (window.location.hash) {
    anchors.some(function (anchor) {
      var found = anchor.getAttribute('href') === window.location.hash;

      if (found) {
        setTimeout(function () {
          var element = findOne(window.location.hash);
          if (element) {
            // Silent scroll to element
            scroll(element, null, offset, true);
          }
        });
      }

      return found;
    });
  }
}

ready(init);

return init;

}());

//# sourceMappingURL=toc.js.map
