import React, { useState } from 'react';
import { Button, Typography } from '@mui/material';
import { ArrowDropDownIcon } from '@mui/x-date-pickers';
import { DatePicker } from '@mui/x-date-pickers/DatePicker';
import moment from 'moment';

import { useSchedulerContext } from '../../../context/SchedulerProvider';
import { useTheme } from '@mui/system';


function ButtonField(props) {
  const {
    setOpen,
    value,
    id,
    disabled,
    InputProps: { ref } = {},
    inputProps: { 'aria-label': ariaLabel } = {},
  } = props;

  const theme = useTheme()
  // Convert the timestamp to a Date object
  const date = new Date(value);
  const handleOpen = () => {
    setOpen?.((prev) => !prev)
  }

  return (
    <Button
      endIcon={<ArrowDropDownIcon />}
      onClick={handleOpen}
      id={id}
      disabled={disabled}
      ref={ref}
      aria-label={ariaLabel}
    >
      <Typography
        sx={{
          textTransform: 'capitalize',
          color: theme.palette.primary.main, 
          fontSize: '18px'
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

  const theme = useTheme()

  const handleOpen = () => {
    setOpen(true)
  }

  const handleClose = () => {
    setOpen(false)
  }

  return (
    <DatePicker
      PopperProps={{
        disablePortal: true,
      }}
      autoOk
      value={date}
      onChange={onDateChange}
      open={open}
      onClose={handleClose}
      onOpen={handleOpen}
      slots={{
        field: ButtonField,
        ...props.slots,
      }}
      slotProps={{
        field: { setOpen },
      }}
      sx={{
        '& .MuiPickersDay-daySelected': {
          backgroundColor: theme.palette.primary.main, // Use main color from theme.palette[color]
          color: theme.palette.primary.contrastText, // Use contrast text color from theme.palette[color]
        },
        '& .MuiPickersDay-daySelected:hover': {
          backgroundColor: theme.palette.primary.main.light, // Use light color from theme.palette[color] on hover
        },
      }}
    />
  );
}

export default SchedulerDatePicker;
