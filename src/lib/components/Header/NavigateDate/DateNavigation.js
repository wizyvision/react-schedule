import React from 'react'
import { IconButton } from '@mui/material';
import { ArrowLeftIcon, ArrowRightIcon } from '@mui/x-date-pickers';

import { useSchedulerContext } from '../../../context/SchedulerProvider';

function ActionButton (props) {
  const { icon, onClick } = props;
  return <IconButton onClick={onClick}>{icon}</IconButton>;
}

function DateNavigation() {
  const { onPrevDate, onNextDate } = useSchedulerContext()

  const actions = [
    <ActionButton icon={<ArrowLeftIcon />} onClick={onNextDate} />,
    <ActionButton icon={<ArrowRightIcon />} onClick={onPrevDate} />,
  ];
  return <div>{actions}</div>;
}

export default DateNavigation