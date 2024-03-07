import React from 'react';
import { Table, TableHead, TableRow, TableBody, Paper } from '@mui/material';

import { useSchedulerContext } from '../../context/SchedulerProvider';
import { generateTimeSlotsForShift } from '../../utils/generateTimeSlot';

import {
  CalendarContainer,
  CalendarRoot,
  Divider,
  Resources,
  Slots,
} from '../../container/Calendar';
import UserTimeSlot from './UserTimeSlot';

function Calendar() {
  const { date, users, SlotProps } = useSchedulerContext();
  const { 
    primaryDuration = 60, 
    secondaryDuration, 
    colSpan
  } = SlotProps || {};

  const classes = useStyles()
 
  const timeSlotsHead = generateTimeSlotsForShift(date, primaryDuration);
  const timeSlotsBody = generateTimeSlotsForShift(date, secondaryDuration);

  return (
    <CalendarContainer component={Paper}>
      <Table sx={classes.table} stickyHeader>
        <TableHead>
          <TableRow sx={{overflowY: 'hidden', backgroundColor: 'white', position: 'sticky', top: 0, zIndex: 1000,}} >
            <Resources>User</Resources>
            <Divider></Divider>
            {timeSlotsHead.map((slot) => (
              <Slots key={slot} colSpan={colSpan}>{slot}</Slots>
            ))}
          </TableRow>
        </TableHead>
        <TableBody>
          {users.map((user) => {
            return (
              <TableRow key={user.name}>
                <Resources align='left'>{user.name}</Resources>
                <Divider align='left'></Divider>
                {timeSlotsBody.map((slot, index) => (
                  <UserTimeSlot
                    key={`${user.name}-${slot}`}
                    index={index}
                    user={user}
                    timeSlot={slot}
                  />
                ))}
              </TableRow>
            );
          })}
        </TableBody>
      </Table>
    </CalendarContainer>
  );
}

const useStyles = () => ({
  table: {
    width: 900,
    overflowX: 'auto',
  },
});

export default Calendar;
