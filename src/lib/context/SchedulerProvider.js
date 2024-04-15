import { ThemeProvider } from '@emotion/react';
import React, { useContext, createContext } from 'react';
import { AdapterDateFns } from '@mui/x-date-pickers/AdapterDateFns';
import { enUS } from 'date-fns/locale';
import { LocalizationProvider } from '@mui/x-date-pickers';
import { DndProvider } from 'react-dnd';
import { HTML5Backend } from 'react-dnd-html5-backend';
import theme from '../constants/theme';

const SchedulerContext = createContext();

const SchedulerProvider = (props) => {
  const {
    children,
    SlotProps,
    AppointmentProps,
    groupId,
    groups,
    users,
    onGroupChange,
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

  const locales = { en: enUS };
  const value = {
    groupId,
    groups,
    users,
    onGroupChange,
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
    <DndProvider backend={HTML5Backend}>
      <SchedulerContext.Provider value={value}>
        <ThemeProvider theme={theme}>
          <LocalizationProvider
            dateAdapter={AdapterDateFns}
            adapterLocale={locales['en']}
          >
            {children}
          </LocalizationProvider>
        </ThemeProvider>
      </SchedulerContext.Provider>
    </DndProvider>
  );
};

const useSchedulerContext = () => {
  return useContext(SchedulerContext);
};

export { SchedulerProvider, useSchedulerContext };
