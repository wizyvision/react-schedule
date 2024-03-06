import React, { createContext, useContext } from 'react';
import { ThemeProvider } from '@mui/material/styles'
import theme from '../../constants/theme';


const SchedulerContext = createContext();

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
  color,
}) =>  {
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
      <ThemeProvider theme={theme} >
        {children}
      </ThemeProvider>
    </SchedulerContext.Provider>
  );
}

const useSchedulerContext = () => {
  return useContext(SchedulerContext);
};

export { SchedulerProvider, useSchedulerContext };
