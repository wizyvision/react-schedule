import React from 'react';
import { IconButton } from '@mui/material';
import { ArrowLeftIcon, ArrowRightIcon } from '@mui/x-date-pickers';

import { useSchedulerContext } from '../../../context/SchedulerProvider';

function ActionButton(props) {
  const { icon, onClick, name } = props;
  return (
    <IconButton key={name} onClick={onClick}>
      {icon}
    </IconButton>
  );
}

function DateNavigation() {
  const { onPrevDate, onNextDate } = useSchedulerContext();

  const actions = [
    <ActionButton
      key='nextDate'
      name='nextDate'
      icon={<ArrowLeftIcon />}
      onClick={onNextDate}
    />,
    <ActionButton
      key='prevDate'
      name='prevDate'
      icon={<ArrowRightIcon />}
      onClick={onPrevDate}
    />,
  ];
  return <div>{actions}</div>;
}

export default DateNavigation;
