import { ThemeProvider } from '@emotion/react';
import React, { useContext, createContext } from 'react';
import theme from '../constants/theme'

const SchedulerContext = createContext();

const SchedulerProvider = (props) => {
  const {
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
  } = props;

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
      <ThemeProvider theme={theme}>
        {children}
      </ThemeProvider>
    </SchedulerContext.Provider>
  );
};

const useSchedulerContext = () => {
  return useContext(SchedulerContext);
};

export { SchedulerProvider, useSchedulerContext };
