import React, { useState } from 'react';
import { Typography, MenuItem, Menu, Button } from '@mui/material';
import { ArrowDropDownIcon } from '@mui/x-date-pickers';

import { useSchedulerContext } from '../../../context/SchedulerProvider';
import { useTheme } from '@mui/system';

function DurationPicker() {
  const { durationOptions, duration, onDurationChange } = useSchedulerContext();
  const theme = useTheme();
  const [anchorEl, setAnchorEl] = useState(null);

  const optionValue = (option) => {
    switch (true) {
      case option === 60:
        return `${option / 60} hour`;
      case option > 59:
        return `${option / 60} hours`;
      case option === 15:
        return `${option} minutes`;
      default:
        return `${option} minutes`;
    }
  };
  const handleButtonClick = (event) => {
    setAnchorEl(event.currentTarget);
  };

  const handleMenuItemClick = (option) => {
    onDurationChange && onDurationChange(option);
    setAnchorEl(null);
  };

  const handleClose = () => {
    setAnchorEl(null);
  };

  const options = durationOptions?.map((option) => (
    <MenuItem
      key={option}
      onClick={() => handleMenuItemClick(option)}
      value={option}
      selected={option === duration}
    >
      {optionValue(option)}
    </MenuItem>
  ));
  return (
    <div style={{ display: 'flex', alignItems: 'center' }}>
      <Typography sx={{ marginRight: '8px' }}>Default Duration:</Typography>
      <Button
        aria-controls='duration-options-menu'
        aria-haspopup='true'
        endIcon={<ArrowDropDownIcon />}
        onClick={handleButtonClick}
        sx={{
          border: 'none',
          textTransform: 'lowercase',
        }}
      >
        <Typography
          sx={{
            color: theme.palette.primary.main, 
            fontSize: '16px'
          }}
        >
          {optionValue(duration)}
        </Typography>
      </Button>
      <Menu
        id='duration-options-menu'
        anchorEl={anchorEl}
        open={Boolean(anchorEl)}
        onClose={handleClose}
      >
        {options}
      </Menu>
    </div>
  );
}

export default DurationPicker;
