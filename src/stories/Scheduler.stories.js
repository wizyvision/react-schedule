import React, { useState } from 'react';
import { DndProvider } from 'react-dnd';
import { HTML5Backend } from 'react-dnd-html5-backend';
import moment from 'moment';

import { users, cases, groups } from '../data/data';

import Scheduler from '../lib/components/Scheduler';
import Events from '../components/Events';
import { createTheme, alpha, ThemeProvider } from '@mui/material/styles';

const theme = createTheme({
  palette: {
    primary: {
      main: '#ff0000'
    }
  },
});

export default {
  title: 'Scheduler',
  component: Scheduler,
  tags: ['autodocs'],
};

const Template = (args) => {
  const [selectedGroup, setGroup] = useState(groups[7].id);
  const [appointments, setAppointments] = useState(
    cases.filter((appointment) => appointment.user && appointment.schedule)
  );
  const [date, setDate] = useState(new Date());
  const [duration, setDuration] = useState(60);

  const colors = ['red', 'blue', 'yellow', 'green', 'orange'];
  const colorMap = {
    red: '#ff0000',
    blue: '#0000ff',
    yellow: '#ffff00',
    green: '#008000',
    orange: '#ffa500'
};


  const handleChangeDate = (newDate) => {
    setDate(newDate);
  };

  const handleChangeDuration = (value) => {
    setDuration(value);
  };

  const handlePrevDate = () => {
    const prevDate = moment(date).add(1, 'days').toDate();
    setDate(prevDate);
  };

  const handleNextDate = () => {
    const nextDate = moment(date).subtract(1, 'days').toDate();
    setDate(nextDate);
  };

  const handleAppointmentChange = (updatedAppointment) => {
    const existingIndex = appointments.findIndex(
      (appointment) => appointment.id === updatedAppointment.id
    );
    if (existingIndex !== -1) {
      // If appointment already exists, update it
      const updatedAppointments = [...appointments];
      updatedAppointments[existingIndex] = updatedAppointment;
      setAppointments(updatedAppointments);
    } else {
      // If appointment doesn't exist, add it to appointmentList
      setAppointments([...appointments, updatedAppointment]);
    }
  };

  const handleGroupChange = (event) => {
    setGroup(event.target.value);
  };

  const list = appointments.map((appointment) => {
    if (appointment.title.includes(appointment.postRef)) {
      return {
        ...appointment,
      };
    }
    return {
      ...appointment,
      title: `${appointment.postRef}: ${appointment.title}`,
    };
  });

  users.forEach((user, index) => {
    const colorIndex = index % colors.length;
    const color = colors[colorIndex];
    user.color = colorMap[color];
  })

  return (
    <ThemeProvider theme={theme}>
      <div >
        <DndProvider backend={HTML5Backend}>
          <div style={{ display: 'flex', alignItems: 'center', width: '100%', overflow: 'hidden' }}>
            <Events unscheduledList={cases} appointmentList={appointments} />
            <Scheduler
              {...args}
              groupId={selectedGroup}
              groups={[...groups, {id: null, name: 'None'}]}
              onGroupChange={handleGroupChange}
              appointmentList={list}
              onAppointmentChange={handleAppointmentChange}
              date={date}
              onDateChange={handleChangeDate}
              onPrevDate={handlePrevDate}
              onNextDate={handleNextDate}
              duration={duration}
              onDurationChange={handleChangeDuration}
              users={users.filter((user) => selectedGroup ? user.groups.includes(selectedGroup): null)}
            />
          </div>
        </DndProvider>
      </div>
    </ThemeProvider>
  );
};

export const ResourceTimeline = Template.bind({});
ResourceTimeline.args = {
  durationOptions: [30, 60, 120],
  SlotProps: {
    secondaryDuration: 30,
    colSpan: 2,
    slotBackground: {
      dropBg: 'rgba(0,0,0,0.08)',
      overBg: 'transparent'
    }
  },
};
