import React from 'react';
import { SchedulerProvider } from '../../context/SchedulerProvider';
import Calendar from '../Calendar';

const Scheduler = (props) => {
    console.log(props)
  return (
    <SchedulerProvider {...props}>
      <div>Hello world</div>
      <Calendar />
    </SchedulerProvider>
  );
};

export default Scheduler