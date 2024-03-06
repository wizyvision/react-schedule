import React, { createContext } from 'react';
import { ThemeProvider } from '@mui/material';
import { createTheme, alpha } from '@mui/material/styles';

const theme = createTheme({
  palette: {
    primary: {
      main: '#303f9f',
      light: '#5e35b1'
    },
    drop: {
      main: alpha('#303f9f', 0.5),
      light: alpha('#303f9f', 0.35),
      mainTwo: alpha('#5e35b1', 0.5),
      lightTwo: alpha('#5e35b1', 0.35)
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

const SchedulerContext = /*#__PURE__*/createContext();
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
  return /*#__PURE__*/React.createElement(SchedulerContext.Provider, {
    value: value
  }, /*#__PURE__*/React.createElement(ThemeProvider, {
    theme: theme
  }, children));
};

const Scheduler = props => {
  return /*#__PURE__*/React.createElement(SchedulerProvider, props, /*#__PURE__*/React.createElement("div", null, "Hello world"));
};

export { Scheduler };
