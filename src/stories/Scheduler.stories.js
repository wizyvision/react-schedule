import React, { useState } from 'react';
import moment from 'moment';

import { users } from '../data/data';

import Scheduler from '../lib/components/Scheduler';

export default {
  title: 'Scheduler',
  component: Scheduler,
  tags: ['autodocs'],
};

const Template = (args) => {
  const [date, setDate] = useState(new Date());
  return (
    <div>
      <Scheduler 
         {...args} 
         date={date} 
         users={users}
      />
    </div>
  );
};

export const ResourceTimeline = Template.bind({});
ResourceTimeline.args = {
  color: 'hello world',
  SlotProps: {
    secondaryDuration: 30,
    colSpan: 2
  }
};
