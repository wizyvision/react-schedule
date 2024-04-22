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
  Avatar,
  darken,
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
  const { date, users, SlotProps, groups, onGroupChange, groupId, resourceLabel } =
    useSchedulerContext();
  const { primaryDuration = 60, secondaryDuration, colSpan } = SlotProps || {};

  const classes = useStyles();

  const timeSlotsHead = generateTimeSlotsForShift(date, primaryDuration);
  const timeSlotsBody = generateTimeSlotsForShift(date, secondaryDuration);

  const tableHead = (
    <TableRow sx={classes.tableRow}>
      <Resources sx={classes.resourceHead} align='left'>
        <Wrapper>
          <Resource>
            <Typography sx={classes.resourceLabelText}>
              {resourceLabel}
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
              value={groupId}
              label='Groups'
              onChange={onGroupChange}
              size='small'
            >
              {/* <MenuItem value={null}>None</MenuItem> */}
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

  const userSlots = users.map((user) => {
      return (
        <TableRow key={user.name}>
          <Resources align='left'>
            <Wrapper>
              <Resource sx={classes.resourceBody}>
                <Avatar sx={classes.avatar(user.color)} variant='square'>
                  {Array.from(user.name)[0]}
                </Avatar>
                {user.name}
              </Resource>
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
  resourceLabelText:{
    fontSize: '16px', 
    fontWeight: 'bold' 
  },
  tableRow: {
    overflowY: 'hidden',
    backgroundColor: 'white',
    position: 'sticky',
    top: 0,
    zIndex: 1000,
  },
  resourceHead: {
    paddingTop: 2,
    paddingBottom: 2,
    paddingRight: 2,
    textTransform: 'capitalize'
  },
  resourceBody: {
    fontSize: '14px',
    display: 'flex',
    alignItems: 'center',
  },
  avatar: (color) => ({
    bgcolor: color,
    marginRight: 2,
    borderColor: darken(color, 0.25),
    color: darken(color, 0.5),
  }),
});

export default Calendar;
