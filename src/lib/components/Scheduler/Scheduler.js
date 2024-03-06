import React from 'react';
import { SchedulerProvider } from './SchedulerProvider';
import Calendar from '../Calendar';

export const Scheduler = (props) => {
  return (
    <SchedulerProvider {...props}>
      <div>Hello world</div>
      <Calendar />
    </SchedulerProvider>
  );
};
