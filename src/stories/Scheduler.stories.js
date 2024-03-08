import React, { useState } from 'react';
import { DndProvider } from 'react-dnd';
import { HTML5Backend } from 'react-dnd-html5-backend';
import { AdapterDateFns } from '@mui/x-date-pickers/AdapterDateFns';
import { enUS } from 'date-fns/locale';
import { LocalizationProvider } from '@mui/x-date-pickers';
import moment from 'moment';

import { users } from '../data/data';

import Scheduler from '../lib/components/Scheduler';

export default {
  title: 'Scheduler',
  component: Scheduler,
  tags: ['autodocs'],
};

const Template = (args) => {
  const locales = { en: enUS };
  const [date, setDate] = useState(new Date());
  const [duration, setDuration] = useState(60)

  const handleChangeDate = (newDate) => {
    setDate(newDate);
  };

  const handleChangeDuration = (value) => {
    setDuration(value)
  }

  const handlePrevDate = () => {
    const prevDate = moment(date).add(1, 'days').toDate()
    setDate(prevDate)
  }

  const handleNextDate = () => {
    const nextDate = moment(date).subtract(1, 'days').toDate()
    setDate(nextDate)
  }

  return (
   <>
      {/* <LocalizationProvider
        dateAdapter={AdapterDateFns}
        adapterLocale={locales['en']}
      >
        <div>
          <DndProvider backend={HTML5Backend}>
            <div>
              <Scheduler
                {...args}
                date={date}
                onDateChange={handleChangeDate}
                onPrevDate={handlePrevDate}
                onNextDate={handleNextDate}
                duration={duration}
                onDurationChange={handleChangeDuration}
                users={users}
              />
            </div>
          </DndProvider>
        </div>
      </LocalizationProvider> */}
   </>
  );
};

export const ResourceTimeline = Template.bind({});
ResourceTimeline.args = {
  color: 'hello world',
  durationOption: [30, 60, 120],
  SlotProps: {
    secondaryDuration: 30,
    colSpan: 2,
  },
};
