'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

var React = require('react');

function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

var React__default = /*#__PURE__*/_interopDefaultLegacy(React);

const SchedulerContext = /*#__PURE__*/React.createContext();
const SchedulerProvider = ({
  children,
  SlotProps,
  AppointmentProps,
  groupId,
  groups,
  users,
  appointmentList,
  onAppointmentChange,
  durationOptions,
  duration = 60,
  onDurationChange,
  date,
  onDateChange,
  onPrevDate,
  onNextDate,
  color
}) => {
  const value = {
    groupId,
    groups,
    users,
    appointmentList,
    onAppointmentChange,
    durationOptions,
    duration,
    onDurationChange,
    date,
    onDateChange,
    onPrevDate,
    onNextDate,
    SlotProps,
    AppointmentProps,
    color
  };
  return /*#__PURE__*/React__default["default"].createElement(SchedulerContext.Provider, {
    value: value
  }, children);
};
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
  return /*#__PURE__*/React__default["default"].createElement(SchedulerProvider, props, /*#__PURE__*/React__default["default"].createElement("div", null, "Hello world"), /*#__PURE__*/React__default["default"].createElement(Calendar, null));
};

exports.Scheduler = Scheduler;
