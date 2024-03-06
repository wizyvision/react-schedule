import React, { createContext, useContext } from 'react';

const SchedulerContext = createContext();

export const SchedulerProvider = ({
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
  color,
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
    color,
  };

  return (
    <SchedulerContext.Provider value={value}>
      {children}
    </SchedulerContext.Provider>
  );
};

export const useSchedulerContext = () => {
  return useContext(SchedulerContext);
};
