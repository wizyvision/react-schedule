'use strict';

var React = require('react');
var SchedulerProvider = require('../../context/SchedulerProvider'); // Import SchedulerProvider

function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

var React__default = /*#__PURE__*/_interopDefaultLegacy(React);

const SchedulerContext = /*#__PURE__*/React.createContext();

const useSchedulerContext = () => {
  return React.useContext(SchedulerContext);
};

function Calendar() {
  const {
    color
  } = useSchedulerContext();
  return /*#__PURE__*/React__default["default"].createElement("div", null, color);
}

const Scheduler = props => {
  console.log(props);
  return /*#__PURE__*/React__default["default"].createElement(SchedulerProvider, props, /*#__PURE__*/React__default["default"].createElement("div", null, "Hello world"), /*#__PURE__*/React__default["default"].createElement(Calendar, null));
};

module.exports = Scheduler;
