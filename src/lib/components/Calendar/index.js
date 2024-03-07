import React from 'react'
import {
  Table,
  TableHead,
  TableRow,
  TableBody,
  Paper,
} from '@mui/material';

import { useSchedulerContext } from '../../context/SchedulerProvider'
import { generateTimeSlotsForShift } from '../../utils/generateTimeSlot';

import { CalendarContainer, CalendarRoot, Divider, Resources, Slots} from '../../container/Calendar'
import Slot from '../../container/Slot';

function Calendar() {
  const {color} = useSchedulerContext()

  return (
    <div>{color}</div>
  )
}

const useStyles = () => ({
  table: {
    width: 900,
    overflowX: 'auto',
  },
});


export default Calendar