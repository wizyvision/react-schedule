import React, { useState } from 'react';
import { Button, Typography } from '@mui/material';
import { ArrowDropDownIcon } from '@mui/x-date-pickers';
import { DatePicker } from '@mui/x-date-pickers/DatePicker';
import moment from 'moment';

import { useSchedulerContext } from '../../../context/SchedulerProvider';


function ButtonField(props) {
  const {
    setOpen,
    value,
    id,
    disabled,
    InputProps: { ref } = {},
    inputProps: { 'aria-label': ariaLabel } = {},
  } = props;
  // Convert the timestamp to a Date object
  const date = new Date(value);

  return (
    <Button
      endIcon={<ArrowDropDownIcon />}
      onClick={() => setOpen?.((prev) => !prev)}
      id={id}
      disabled={disabled}
      ref={ref}
      aria-label={ariaLabel}
    >
      <Typography
        sx={{
          textTransform: 'capitalize',
        }}
      >
        {moment(date).format('ddd, MMM DD, YYYY')}
      </Typography>
    </Button>
  );
}

function SchedulerDatePicker(props) {
  const { date, onDateChange } = useSchedulerContext();
  const [open, setOpen] = useState(false);
  return (
    <DatePicker
      PopperProps={{
        disablePortal: true,
      }}
      autoOk
      value={date}
      onChange={onDateChange}
      open={open}
      onClose={() => setOpen(false)}
      onOpen={() => setOpen(true)}
      slots={{
        field: ButtonField,
        ...props.slots,
      }}
      slotProps={{
        field: { setOpen },
      }}
    />
  );
}

export default SchedulerDatePicker;
