import React from 'react';
import {
  Table,
  TableHead,
  TableRow,
  TableBody,
  Paper,
  Select,
  MenuItem,
  InputLabel,
  FormControl,
  Typography,
} from '@mui/material';

import { useSchedulerContext } from '../../context/SchedulerProvider';
import { generateTimeSlotsForShift } from '../../utils/generateTimeSlot';

import {
  CalendarContainer,
  Divider,
  Resources,
  Resource,
  Slots,
  Wrapper,
} from '../../container/Calendar';
import UserTimeSlot from './UserTimeSlot';

function Calendar() {
  const { date, users, SlotProps, groups, onGroupChange, groupId } =
    useSchedulerContext();
  const { primaryDuration = 60, secondaryDuration, colSpan } = SlotProps || {};

  const classes = useStyles();

  const timeSlotsHead = generateTimeSlotsForShift(date, primaryDuration);
  const timeSlotsBody = generateTimeSlotsForShift(date, secondaryDuration);

  const tableHead = (
    <TableRow
      sx={{
        overflowY: 'hidden',
        backgroundColor: 'white',
        position: 'sticky',
        top: 0,
        zIndex: 1000,
      }}
    >
      <Resources sx={{ paddingTop: 2, paddingBottom: 2, paddingRight: 2 }} align='left'>
        <Wrapper>
          <Resource>
            <Typography sx={{ fontSize: '16px', fontWeight: 'bold' }}>
              Users
            </Typography>
          </Resource>
          <Divider></Divider>
        </Wrapper>
        <Resource sx={{ marginTop: 2 }}>
          <FormControl size='small' fullWidth>
            <InputLabel id='groups'>Groups</InputLabel>
            <Select
              labelId='groups'
              id='groups'
              value={groupId || 0}
              label='Groups'
              onChange={onGroupChange}
              size='small'
            >
              <MenuItem value={0}>All</MenuItem>
              {groups.map((group) => (
                <MenuItem value={group.id}>{group.name}</MenuItem>
              ))}
            </Select>
          </FormControl>
        </Resource>
      </Resources>
      {timeSlotsHead.map((slot) => (
        <Slots key={slot} colSpan={colSpan}>
          {slot}
        </Slots>
      ))}
    </TableRow>
  );

  const userSlots = users
    .filter((user) => {
      if (groupId) {
        return user.groups.includes(groupId);
      }
      return user;
    })
    .map((user) => {
      return (
        <TableRow key={user.name}>
          <Resources align='left'>
            <Wrapper>
              <Resource sx={{ fontSize: '14px' }}>{user.name}</Resource>
              <Divider></Divider>
            </Wrapper>
          </Resources>
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
    });

  return (
    <CalendarContainer component={Paper}>
      <Table sx={classes.table} stickyHeader>
        <TableHead>{tableHead}</TableHead>
        <TableBody>{userSlots}</TableBody>
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
