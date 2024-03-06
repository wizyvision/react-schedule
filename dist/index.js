'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

var React = require('react');
var material = require('@mui/material');
var styles = require('@mui/material/styles');

function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

var React__default = /*#__PURE__*/_interopDefaultLegacy(React);

const theme = styles.createTheme({
  palette: {
    primary: {
      main: '#303f9f',
      light: '#5e35b1'
    },
    drop: {
      main: styles.alpha('#303f9f', 0.5),
      light: styles.alpha('#303f9f', 0.35),
      mainTwo: styles.alpha('#5e35b1', 0.5),
      lightTwo: styles.alpha('#5e35b1', 0.35)
    },
    slotBg: {
      main: 'transparent'
    },
    drag: {
      main: '#E0E0E0'
    },
    borderRightColor: {
      main: '#666666',
      light: 'rgba(0, 0, 0, 0.05)'
    }
  }
});

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
  }, /*#__PURE__*/React__default["default"].createElement(material.ThemeProvider, {
    theme: theme
  }, children));
};

const Scheduler = props => {
  return /*#__PURE__*/React__default["default"].createElement(SchedulerProvider, props, /*#__PURE__*/React__default["default"].createElement("div", null, "Hello world"));
};

exports.Scheduler = Scheduler;
