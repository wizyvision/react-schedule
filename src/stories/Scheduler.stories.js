import React from 'react';

import Scheduler from '../lib/components/Scheduler'

export default {
  title: 'Scheduler',
  component: Scheduler,
  tags: ['autodocs'],
};

const Template = (args) => {
  return (<Scheduler {...args} />);
};

export const ResourceTimeline = Template.bind({});
ResourceTimeline.args = {
  color: 'hello world'
}
