import React, { createContext, useContext } from 'react';

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
  }, children);
};
const useSchedulerContext = () => {
  return useContext(SchedulerContext);
};

function Calendar() {
  const {
    color
  } = useSchedulerContext();
  return /*#__PURE__*/React.createElement("div", null, color);
}

const Scheduler = props => {
  return /*#__PURE__*/React.createElement(SchedulerProvider, props, /*#__PURE__*/React.createElement("div", null, "Hello world"), /*#__PURE__*/React.createElement(Calendar, null));
};

export { Scheduler };
