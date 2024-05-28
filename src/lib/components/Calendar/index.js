import React, { useState, useEffect } from 'react';
import {
  Table,
  TableHead,
  TableRow,
  TableBody,
  Select,
  MenuItem,
  InputLabel,
  FormControl,
  Typography,
} from '@mui/material';

import { useSchedulerContext } from '../../context/SchedulerProvider';
import { generateTimeSlotsForShift } from '../../utils/generateTimeSlot';

import {
  StyledTableContainer,
  StickyCell,
  ResourceCell,
  TimeSlots,
  StyledBox,
} from '../../container/Calendar';
import UserTimeSlot from './UserTimeSlot';
import { MIN_ROWS } from '../../constants/appointment';
import Slot from '../../container/Slot';
import { getSlotWidth } from '../../utils/getAppointmentStyle';
import ResourceName from './ResourceName';

function Calendar() {
  const {
    date,
    users,
    SlotProps,
    groups,
    onGroupChange,
    groupId,
    resourceLabel,
    minRows,
    isLoading,
    groupLabel,
  } = useSchedulerContext();
  const { primaryDuration = 60, secondaryDuration, colSpan } = SlotProps || {};

  const classes = useStyles();

  const timeSlotsHead = generateTimeSlotsForShift(date, primaryDuration);
  const timeSlotsBody = generateTimeSlotsForShift(date, secondaryDuration);
  const [additionalRows, setAdditionalRows] = useState(0);

  const minimumRows = minRows || MIN_ROWS;

  useEffect(() => {
    if (users.length <= minimumRows) {
      setAdditionalRows(minimumRows - users.length);
    } else {
      setAdditionalRows(0);
    }
  }, [users]);

  const tableHead = (
    <TableRow sx={classes.tableRow}>
      <StickyCell sx={classes.resourceHead} align='left'>
        <StyledBox>
          <ResourceCell>
            <Typography sx={classes.resourceLabelText}>
              {resourceLabel}
            </Typography>
          </ResourceCell>
        </StyledBox>
        <ResourceCell sx={{ marginTop: 2 }}>
          <FormControl size='small' fullWidth>
            <InputLabel id='groups'>{groupLabel || 'Groups'}</InputLabel>
            <Select
              labelId='groups'
              id='groups'
              value={groupId}
              label={groupLabel || 'Groups'}
              onChange={onGroupChange}
              size='small'
            >
              {groups.map((group) => (
                <MenuItem value={group.id}>{group.name}</MenuItem>
              ))}
            </Select>
          </FormControl>
        </ResourceCell>
      </StickyCell>
      {timeSlotsHead.map((slot) => (
        <TimeSlots key={slot} colSpan={colSpan}>
          {slot}
        </TimeSlots>
      ))}
    </TableRow>
  );

  const userSlots = users.map((user) => {
    return (
      <TableRow key={user.name}>
        <StickyCell align='left'>
          <ResourceCell sx={classes.resourceBody}>
            <ResourceName name={user.name} color={user.color} />
          </ResourceCell>
        </StickyCell>
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

  const width = getSlotWidth(secondaryDuration);

  const emptySlots = timeSlotsBody.map((slot, index) => (
    <Slot
      key={index}
      colSpan={1}
      width={width}
      sx={{ borderBottom: isLoading && 'none' }}
    >
      <div style={{ width: width, height: '100%' }}>&nbsp;</div>
    </Slot>
  ));

  const additionalRowsContent = Array.from(
    { length: !isLoading && users.length ? additionalRows : minimumRows },
    (_, index) => (
      <TableRow key={`additional-row-${index}`}>
        <StickyCell
          align='left'
          sx={{
            borderBottom: isLoading && 'none',
          }}
        >
          <StyledBox>
            <ResourceCell sx={classes.resourceBody}></ResourceCell>
          </StyledBox>
        </StickyCell>
        {emptySlots}
      </TableRow>
    )
  );

  return (
    <StyledTableContainer>
      <Table sx={classes.table} stickyHeader>
        <TableHead>{tableHead}</TableHead>
        <TableBody>
          {!isLoading && userSlots}
          {additionalRowsContent}
        </TableBody>
      </Table>
    </StyledTableContainer>
  );
}

const useStyles = () => ({
  table: {
    width: '100%',
    height: '100%',
  },
  resourceLabelText: {
    fontSize: '16px',
    fontWeight: 'bold',
  },
  tableRow: {
    backgroundColor: 'white',
    position: 'sticky',
    top: 0,
    zIndex: 1000,
  },
  resourceHead: {
    paddingTop: 2,
    paddingBottom: 2,
    paddingRight: 2,
    textTransform: 'capitalize',
  },
  resourceBody: {
    fontSize: '14px',
    display: 'flex',
    alignItems: 'center',
  },
});

export default Calendar;
