import React from 'react';
import { SchedulerProvider } from './SchedulerProvider';

export const Scheduler = (props) => {
  return (
    <SchedulerProvider {...props}>
      <div>Hello world</div>
    </SchedulerProvider>
  );
};
