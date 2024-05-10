import React from 'react';

import { Button } from '@mui/material'
import { useSchedulerContext } from '../../../context/SchedulerProvider';

function TodayButton() {
  const { onDateChange } = useSchedulerContext();
  function handleDateChange() {
    const dateNow = new Date();
    onDateChange(dateNow);
  }
  return (
    <Button 
        onClick={handleDateChange} 
        sx={{ textTransform: 'capitalize', fontSize: '16px' }}
        >
      Today
    </Button>
  );
}

export default TodayButton;
