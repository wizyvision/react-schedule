import { TableCell, useTheme, lighten } from '@mui/material';
import { HEIGHT } from '../../constants/appointment';
import { slotBg } from '../../utils/getAppointmentStyle';
import { useSchedulerContext } from '../../context/SchedulerProvider';
import { styled } from '@mui/system'

const Slot = styled(TableCell)((props) => {
  const { color = "primary", SlotProps, } = useSchedulerContext()
  const { index, canDrop, isOver, width } = props;
  const { secondaryDuration = 30, style, slotBackground} = SlotProps || {};
  const theme = useTheme()

  const bg = slotBg(canDrop, isOver, slotBackground, theme, color);

  // const borderRightColor = () => {
  //   let color = theme.palette.borderRightColor.light
  //   switch (secondaryDuration) {
  //     case 15:
  //       color = index % 4 !== 3 ? 
  //       theme.palette.borderRightColor.light
  //       : theme.palette.borderRightColor.main; 
  //       break;
  //     default:
  //       color = index % 2 !== 1 ? 
  //       theme.palette.borderRightColor.light
  //       : theme.palette.borderRightColor.main; 
  //       break;
  //   }
  //   return color;
  // };

  // const borderRightStyle = () => {
  //   switch (secondaryDuration) {
  //     case 15:
  //       if (index % 2 !== 1) {
  //         return 'none';
  //       }
  //       return 'solid';
  //     default:
  //       return 'solid';
  //   }
  // };

  return {
    paddingTop: theme.spacing(1),
    paddingBottom: theme.spacing(1),
    paddingLeft: 0,
    paddingRight: 0,
    position: 'relative',
    backgroundColor: bg,
    width: width,
    height: HEIGHT,
    overflow: 'visible',
    verticalAlign: 'top',
    borderRightWidth: '1px',
    borderRightStyle: 'solid',
    borderRightColor: theme.palette.borderRightColor.light,
    // borderRightStyle: borderRightStyle(),
    ...style,
  };
});

export default Slot;
